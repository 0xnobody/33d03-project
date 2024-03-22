using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;
using System.Security.AccessControl;
using Microsoft.VisualBasic;

namespace _33D03.Server
{
    delegate void PacketReceived(TxpClientState clientState, byte[] data);

    internal class TxpClientState
    {
        public uint ConverstaionId;
        public uint IncomingSequenceNumber;
        public uint OutgoingSequenceNumber;
        public byte[] PacketBuffer;
        public IPEndPoint LastEndPoint;

        public AutoResetEvent AckReceivedEvent = new AutoResetEvent(false);
        public Shared.Txp.Interface.AckType AckType;

        public TxpClientState(uint converstaionId, IPEndPoint initialEndPoint)
        {
            ConverstaionId = converstaionId;
            IncomingSequenceNumber = 0;
            OutgoingSequenceNumber = 0;
            PacketBuffer = new byte[0];
            LastEndPoint = initialEndPoint;
        }
    }

    internal class TxpServer
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private UdpClient server;

        // TODO: cleanup converstaions after no activity after a while
        public Dictionary<uint, TxpClientState> converstaions = new Dictionary<uint, TxpClientState>();

        private Thread listenerThread;

        public event PacketReceived OnPacketReceived;
        
        public TxpServer(int port)
        {
            server = new UdpClient(port);
            listenerThread = new Thread(ListenForPackets);
        }

        public void Start()
        {
            listenerThread.Start();
        }
        public void Send(byte[] data, TxpClientState destination, int attempts = 3)
        {
            if (attempts == 0)
            {
                throw new Exception("Failed to send data after 3 attempts");
            }

            var packetsToQueue = SerializeData(data, destination);

            foreach (var packet in packetsToQueue)
            {
                logger.Debug($"Sending packet to cid {destination.ConverstaionId} at {destination.LastEndPoint} with sn {packet.Item1}");

                server.Send(packet.Item2, packet.Item2.Length, destination.LastEndPoint);

                // Wait for the ACK/NACK for a certain timeout
                if (destination.AckReceivedEvent.WaitOne(TimeSpan.FromMilliseconds(Shared.Txp.Constants.ACK_TIMEOUT_MS)))
                {
                    if (destination.AckType == Shared.Txp.Interface.AckType.Ack)
                    {
                        // ACK received
                        logger.Debug($"ACK received for sn {packet.Item1}");
                    }
                    else
                    {
                        // NACK received
                        logger.Warn($"NACK received for sn {packet.Item1}");

                        // Resend packet, decrease attempt number
                        Send(data, destination, attempts - 1);
                    }
                }
                else
                {
                    // Timeout or NACK received, resend packet
                    logger.Warn($"Timeout passed for sn {packet.Item1}, resending");

                    // Resend packet, decrease attempt number
                    Send(data, destination, attempts - 1);
                }
            }

            // Reset outgoing sn after full packet is sent.
            destination.OutgoingSequenceNumber = 0;
        }

        private void HandleIncomingClientPacket(TxpClientState converstaion, Shared.Txp.Header header, byte[] receivedData)
        {
            switch (header.type)
            {
                case Shared.Txp.PacketType.Data:
                    logger.Debug($"Received {converstaion.ConverstaionId} data packet with sn {header.seqNum}");

                    var lengthOfDataReceived = receivedData.Length - Shared.Txp.Constants.HEADER_SIZE;

                    if (converstaion.IncomingSequenceNumber == header.seqNum)
                    {
                        var previousBufferLength = converstaion.PacketBuffer.Length;
                        Array.Resize(ref converstaion.PacketBuffer, converstaion.PacketBuffer.Length + lengthOfDataReceived);
                        Buffer.BlockCopy(receivedData, Shared.Txp.Constants.HEADER_SIZE, converstaion.PacketBuffer, previousBufferLength, lengthOfDataReceived);
                        converstaion.IncomingSequenceNumber++;

                        // logger.Trace($"Current {converstaion.ConverstaionId} buffer state: {BitConverter.ToString(converstaion.PacketBuffer)}");

                        if (header.finish == 1)
                        {
                            OnPacketReceived(converstaion, converstaion.PacketBuffer);

                            converstaion.IncomingSequenceNumber = 0;
                            converstaion.PacketBuffer = new byte[0];
                        }

                        SendAck(header.seqNum, converstaion.ConverstaionId, converstaion.LastEndPoint);
                    }
                    else if (converstaion.IncomingSequenceNumber > header.seqNum)
                    {
                        // NACK
                        logger.Warn($"Received out of order packet with sn {header.seqNum}");

                        SendNack(header.seqNum, converstaion.ConverstaionId, converstaion.LastEndPoint);
                    }
                    else
                    {
                        logger.Warn($"Received a repeat packet that has already been processed with sn {header.seqNum}. Ignoring.");
                    }

                    break;
                case Shared.Txp.PacketType.ACK:
                    converstaion.AckType = Shared.Txp.Interface.AckType.Ack;
                    converstaion.AckReceivedEvent.Set();
                    break;
                case Shared.Txp.PacketType.NACK:
                    converstaion.AckType = Shared.Txp.Interface.AckType.Nack;
                    converstaion.AckReceivedEvent.Set();
                    break;
            }
        }

        private void ListenForPackets()
        {
            while (true)
            {
                IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Any, 0);

                byte[] receivedData = server.Receive(ref remoteEndPoint);

                if (receivedData.Length < Shared.Txp.Constants.HEADER_SIZE)
                {
                    logger.Log(NLog.LogLevel.Error, "Received data is too small to be a packet");

                    throw new Exception("Received data is too small to be a packet");
                }

                var header = Shared.Txp.Header.FromBytes(receivedData);

                if (!header.IsValid(receivedData))
                {
                    logger.Warn($"Packet received from {remoteEndPoint} is invalid (magic {header.magic:X}, csum {header.checksum:X}), ignoring");

                    //
                    // We can't send a NACK here, as the convId may also be invalid.
                    // So we just wait for a retransmission.
                    //

                    continue;
                }

                logger.Trace($"Received valid packet from of type {Enum.GetName(typeof(Shared.Txp.PacketType), header.type)}");

                if (converstaions.ContainsKey(header.convId) == false)
                {
                    converstaions.Add(header.convId, new TxpClientState(header.convId, remoteEndPoint));
                }

                var converstaion = converstaions[header.convId];

                // Update the end-point in case it changed, ie. the client switched networks
                converstaion.LastEndPoint = remoteEndPoint;

                var clientThread = new Thread(() => HandleIncomingClientPacket(converstaion, header, receivedData));
                clientThread.Start();
            }
        }
        private List<Tuple<uint, byte[]>> SerializeData(byte[] data, TxpClientState destination)
        {
            return Shared.Txp.Interface.SerializeData(data, destination.ConverstaionId, ref destination.OutgoingSequenceNumber);
        }

        private Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final, TxpClientState destination)
        {
            return Shared.Txp.Interface.CreatePacket(rawData, final, destination.ConverstaionId, ref destination.OutgoingSequenceNumber);
        }

        //
        // TODO: Perhaps we should also include / verify the checksum for ACK and NACK packets?
        //

        private void SendAck(uint sequenceNumber, uint conversationId, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = conversationId,
                seqNum = sequenceNumber,
                finish = 1,
                type = Shared.Txp.PacketType.ACK
            };

            byte[] ackPacket = header.ToBytes();
            server.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }

        private void SendNack(uint sequenceNumber, uint conversationId, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = conversationId,
                seqNum = sequenceNumber,
                finish = 1,
                type = Shared.Txp.PacketType.NACK
            };

            byte[] ackPacket = header.ToBytes();
            server.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }
    }
}
