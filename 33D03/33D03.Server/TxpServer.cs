﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;
using System.Security.AccessControl;
using Microsoft.VisualBasic;
using _33D03.Shared.Pip;
using _33D03.Shared.Txp;
using System.Security.Cryptography;

namespace _33D03.Server
{
    delegate void PacketReceived(TxpClientConversation clientConversation, byte[] data);
    delegate void ClientDisconnected(TxpClientConversation clientConversation);

    // Manages conversation state with a client, including sequence numbers and the last known endpoint.
    internal class TxpClientConversation
    {
        // Unique identifier for the conversation.
        public uint ConversationId;
        // The last known endpoint from which the client sent a packet.
        public IPEndPoint LastEndPoint;

        public SegmentHandler SegmentHandler;

        public SynHandler SynHandler;

        // Initializes a new conversation with a client.
        public TxpClientConversation(UdpClient client, uint conversationId, IPEndPoint initialEndPoint)
        {
            ConversationId = conversationId;
            LastEndPoint = initialEndPoint; // Store the client's endpoint.
            SegmentHandler = new SegmentHandler(client, conversationId);
            SynHandler = new SynHandler(client, initialEndPoint, conversationId);
        }
    }

    // Implements the server logic for handling TXP (a hypothetical protocol) clients and their data packets.
    internal class TxpServer
    {
        // Logger for recording server events and errors.
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        // UDP client used by the server to receive and send data.
        private UdpClient server;

        // Dictionary mapping conversation IDs to client conversation states.
        public Dictionary<uint, TxpClientConversation> conversations = new Dictionary<uint, TxpClientConversation>();
        private uint currentConversationId = 1;

        private Mutex conversationsMutex = new Mutex(); // TODO: implement thread-safe conversation access

        // Event triggered when a complete data packet is received.
        public event PacketReceived OnPacketReceived;

        public event ClientDisconnected OnClientDisconnected;

        public bool IsRunning { get; private set; }

        // Initializes the server to listen on the specified port.
        public TxpServer(int port)
        {
            server = new UdpClient(port); // Bind the server to the specified port.
            server.DontFragment = true;
        }

        // Starts the server's listening thread, beginning packet reception.
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
        }

        public void Stop()
        {
            IsRunning = false;
            server.Close();
        }

        /// <summary>
        /// Send the specified data to the specified client. Can be called from any thread.
        /// </summary>
        /// <param name="data"></param>
        /// <param name="conversation"></param>
        public void Send(byte[] data, TxpClientConversation conversation)
        {
            conversation.SegmentHandler.SendOrQueuePacket(data, conversation.LastEndPoint);
        }

        /// <summary>
        /// Broadcast the specified data to all connected clients. Can be called from any thread.
        /// </summary>
        /// <param name="data"></param>
        public void Broadcast(byte[] data)
        {
            foreach (var conv in conversations.Values)
            {
                Send(data, conv);
            }
        }

        private void disconnectClient(TxpClientConversation conversation)
        {
            OnClientDisconnected(conversation);
            conversations.Remove(conversation.ConversationId);
        }

        private void ListenForData()
        {
            IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Any, 0);

            var pckt = Shared.Txp.Interface.ListenForPacket(server, ref remoteEndPoint);
            if (pckt == null)
            {
                logger.Warn("Something went wrong in listening for data");
                throw new Exception("Received null response from ListenForPacket");
            }

            var header = pckt.Item1;
            var receivedData = pckt.Item2;

            TxpClientConversation conversation = null;

            lock (conversationsMutex)
            {
                if (header.type == Shared.Txp.PacketType.PING_REQ)
                {
                    var cid = currentConversationId++;
                    conversation = new TxpClientConversation(server, cid, remoteEndPoint);
                    conversations.Add(cid, conversation);
                    sendCID(conversation.ConversationId, remoteEndPoint);
                    conversation.SynHandler.Start(); // Start sending periodic SYNs

                    conversation.SynHandler.OnMaxSYNAttemptsReached += () =>
                    {
                        logger.Warn($"Client {remoteEndPoint} did not respond to SYN-ACK, purging conversation ID {conversation.ConversationId}");
                        disconnectClient(conversation);
                    };
                    return;
                }
                else
                {
                    if (!conversations.TryGetValue(header.convId, out conversation))
                    {
                        logger.Warn($"Conversation {header.convId:X} not found in server list");
                        return;
                    }
                }
            }

            // Update the conversation's last known endpoint. This is important if the client's network address changes.
            conversation.LastEndPoint = remoteEndPoint;

            conversation.SynHandler.RefreshSYNTimeout(remoteEndPoint);

            switch (header.type)
            {
                case Shared.Txp.PacketType.Data:
                    conversation.SegmentHandler.SegmentReceived(header.seqNum, header.pcktNum, header.finish == 1, header.GetContainedData(receivedData), remoteEndPoint);

                    if (conversation.SegmentHandler.FullPacketReady())
                    {
                        OnPacketReceived(conversation, conversation.SegmentHandler.ConsumeFullPacket());
                    }
                    break;
                case Shared.Txp.PacketType.ACK:
                    conversation.SegmentHandler.AckReceived(header.seqNum, header.pcktNum);

                    if (conversation.SegmentHandler.AllAcksReceived())
                    {
                        conversation.SegmentHandler.SendNextPacketIfReady(remoteEndPoint);
                    }
                    break;
                case Shared.Txp.PacketType.NACK:
                    conversation.SegmentHandler.NackReceived(header.seqNum, header.pcktNum, remoteEndPoint);
                    break;
                case Shared.Txp.PacketType.SYN:
                    conversation.SynHandler.RespondToSYN(remoteEndPoint);
                    break;
                case Shared.Txp.PacketType.SYN_ACK:
                    conversation.SynHandler.SYNACKReceived();
                    break;
                case Shared.Txp.PacketType.RESET:
                    OnClientDisconnected(conversation);
                    conversations.Remove(header.convId);
                    break;
                default:
                    logger.Warn("Received unknown packet type");
                    break;
            }
        }

        private void sendCID(uint cid, IPEndPoint endpoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = cid,
                seqNum = 0,
                pcktNum = 0,
                finish = 1,
                type = Shared.Txp.PacketType.PING_RES
            };

            header.checksum = header.CalculateChecksum(header.ToBytes());

            logger.Info($"Assigning cid {cid:X} to client at {endpoint}");

            byte[] ackPacket = header.ToBytes();
            server.Send(ackPacket, ackPacket.Length, endpoint);
        }
    }
}
