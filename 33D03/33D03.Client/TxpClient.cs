﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared;
using System.Runtime.InteropServices;
using Microsoft.VisualBasic;
using Microsoft.Z3;
using Newtonsoft.Json.Converters;

namespace _33D03.Client
{
    // Delegate for handling received packets.
    public delegate void PacketReceived(byte[] data);
    public delegate void ServerDisconnected();

    public class TxpClient
    {
        // Logger instance for logging messages.
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        // UDP client for sending and receiving data.
        private UdpClient client;
        // Server endpoint to send data to and receive data from.
        private IPEndPoint serverEndPoint;

        // A unique identifier for the conversation between this client and the server.
        private uint conversationId = 0;

        // Buffers packets for reassembly.
        private Shared.Txp.SegmentHandler segmentHandler;

        private Shared.Txp.SynHandler synHandler;

        private ManualResetEvent cidAssignedEvent = new ManualResetEvent(false);

        // Event triggered upon receiving a complete packet.
        public event PacketReceived OnPacketReceived;

        public event ServerDisconnected OnServerDisconnected;

        public bool IsRunning { get; private set; }

        // Constructor: initializes client, server endpoint, conversation ID, and starts listening thread.
        public TxpClient(string endpoint, int serverPort)
        {
            // Initialize the UDP client to bind to any available port.
            client = new UdpClient(0);
            client.DontFragment = true;

            try
            {
                // Parse the server IP and port into an IPEndPoint.
                serverEndPoint = new IPEndPoint(IPAddress.Parse(endpoint), serverPort);
            }
            catch (FormatException ex)
            {
                var addresses = Dns.GetHostAddresses(endpoint);

                if (!addresses.Any())
                {
                    throw new Exception("Invalid server IP address or hostname.");
                }

                serverEndPoint = new IPEndPoint(addresses[1], serverPort);
            }

            // Initialize the packet bufferer for handling packet fragments.
            segmentHandler = new Shared.Txp.SegmentHandler(client, conversationId);

            synHandler = new Shared.Txp.SynHandler(client, serverEndPoint, conversationId);

            synHandler.OnMaxSYNAttemptsReached += () =>
            {
                logger.Warn("Max SYN attempts reached, server is likely down.");
                OnServerDisconnected?.Invoke();
                Close();
            };

            synHandler.Start();
        }

        // Starts the listening thread for incoming data.
        public void Start()
        {
            IsRunning = true;

            new Thread(() =>
            {
                while (IsRunning)
                {
                    ListenForData();
                }
            }).Start();

            // Block until we receive a CID from the server.
            //
            do
            {
                RequestCID();
            }
            while (!cidAssignedEvent.WaitOne(2500));
        }
        
        public void Close()
        {
            //
            // TODO: send RESET message to server
            //
            IsRunning = false;
            client.Close();
        }

        /// <summary>
        /// Send or queue data to be sent to the server.
        /// Can be invoked from multiple threads.
        /// </summary>
        /// <param name="data"></param>
        public void Send(byte[] data)
        {
            logger.Trace($"Sending packet {BitConverter.ToString(data).Replace("-", "")}");

            segmentHandler.SendOrQueuePacket(data, serverEndPoint);
        }

        private void ListenForData()
        {
            IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Loopback, 0000);

            var pckt = Shared.Txp.Interface.ListenForPacket(client, ref remoteEndPoint);
            if (pckt == null)
            {
                logger.Warn("Something went wrong in listening for data");
                throw new Exception("Received null response from ListenForPacket");
            }

            var header = pckt.Item1;
            var receivedData = pckt.Item2;

            if (header.type == Shared.Txp.PacketType.PING_RES)
            {
                HandleCIDAssignment(header.convId);
                return;
            }

            synHandler.RefreshSYNTimeout(remoteEndPoint);

            if (header.convId != conversationId)
            {
                logger.Warn($"Received wrong conversation ID {conversationId}");
            }

            switch (header.type)
            {
                case Shared.Txp.PacketType.Data:
                    segmentHandler.SegmentReceived(header.seqNum, header.pcktNum, header.finish == 1, header.GetContainedData(receivedData), remoteEndPoint);

                    if (segmentHandler.FullPacketReady())
                    {
                        OnPacketReceived(segmentHandler.ConsumeFullPacket());
                    }
                    break;
                case Shared.Txp.PacketType.ACK:
                    segmentHandler.AckReceived(header.seqNum, header.pcktNum);

                    segmentHandler.SendNextPacketIfReady(remoteEndPoint);

                    break;
                case Shared.Txp.PacketType.NACK:
                    segmentHandler.NackReceived(header.seqNum, header.pcktNum, remoteEndPoint);
                    break;
                case Shared.Txp.PacketType.SYN:
                    synHandler.RespondToSYN(remoteEndPoint);
                    break;
                case Shared.Txp.PacketType.SYN_ACK:
                    synHandler.SYNACKReceived();
                    break;
                case Shared.Txp.PacketType.RESET:
                    OnServerDisconnected();
                    Close();
                    break;
                default:
                    logger.Warn("Received unknown packet type");
                    break;
            }
        }

        private void RequestCID()
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = 0,
                seqNum = 0,
                pcktNum = 0,
                finish = 1,
                type = Shared.Txp.PacketType.PING_REQ
            };

            header.checksum = header.CalculateChecksum(header.ToBytes());

            logger.Info($"Requesting CID");

            byte[] ackPacket = header.ToBytes();
            client.Send(ackPacket, ackPacket.Length, serverEndPoint);
        }

        private void HandleCIDAssignment(uint cid)
        {
            conversationId = cid;
            segmentHandler.AssignCID(cid);
            synHandler.AssignCID(cid);

            logger.Info($"Client assigned cid {cid:X}");

            cidAssignedEvent.Set();
        }
    }
}