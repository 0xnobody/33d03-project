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
    delegate void PacketReceived(TxpClientConversation clientconversation, byte[] data);

    internal class TxpClientConversation
    {
        public uint ConversationId;
        public uint IncomingSequenceNumber;
        public uint OutgoingSequenceNumber;
        public IPEndPoint LastEndPoint;

        public Shared.Txp.AckHandler AckHandler;
        public Shared.Txp.PacketBufferer PacketBufferer;

        public TxpClientConversation(UdpClient client, uint conversationId, IPEndPoint initialEndPoint)
        {
            ConversationId = conversationId;
            IncomingSequenceNumber = 0;
            OutgoingSequenceNumber = 0;
            LastEndPoint = initialEndPoint;

            AckHandler = new Shared.Txp.AckHandler(client, conversationId);
            PacketBufferer = new Shared.Txp.PacketBufferer();
        }
    }

    internal class TxpServer
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private UdpClient server;

        // TODO: cleanup conversations after no activity after a while
        public Dictionary<uint, TxpClientConversation> conversations = new Dictionary<uint, TxpClientConversation>();

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
        public void Send(byte[] data, TxpClientConversation conversation, int attempts = 3)
        {
            if (attempts == 0)
            {
                throw new Exception("Failed to send data after 3 attempts");
            }

            var packetsToQueue = SerializeData(data, conversation);

            foreach (var packet in packetsToQueue)
            {
                logger.Debug($"Sending packet to cid {conversation.ConversationId} at {conversation.LastEndPoint} with sn {packet.Item1}");

                server.Send(packet.Item2, packet.Item2.Length, conversation.LastEndPoint);

                // Wait for the ACK/NACK for a certain timeout
                if (conversation.AckHandler.WaitForAckOrTimeout() == Shared.Txp.AckAction.Rebroadcast)
                {
                    logger.Warn($"Timeout passed for sn {packet.Item1}, resending");

                    // Resend packet, decrease attempt number
                    Send(data, conversation, attempts - 1);
                }
            }

            // Reset outgoing sn after full packet is sent.
            conversation.OutgoingSequenceNumber = 0;
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

                if (conversations.ContainsKey(header.convId) == false)
                {
                    conversations.Add(header.convId, new TxpClientConversation(server, header.convId, remoteEndPoint));
                }

                var conversation = conversations[header.convId];

                // Update the end-point in case it changed, ie. the client switched networks
                conversation.LastEndPoint = remoteEndPoint;

                switch (header.type)
                {
                    case Shared.Txp.PacketType.Data:
                        logger.Debug($"Received {conversation.ConversationId} data packet with sn {header.seqNum}");

                        var lengthOfDataReceived = receivedData.Length - Shared.Txp.Constants.HEADER_SIZE;

                        if (conversation.IncomingSequenceNumber == header.seqNum)
                        {
                            conversation.PacketBufferer.AddPacket(header.GetContainedData(receivedData));
                            conversation.IncomingSequenceNumber++;

                            // logger.Trace($"Current {conversation.conversationId} buffer state: {BitConverter.ToString(conversation.PacketBuffer)}");

                            conversation.AckHandler.SendAck(header.seqNum, conversation.LastEndPoint);

                            if (header.finish == 1)
                            {
                                OnPacketReceived(conversation, conversation.PacketBufferer.ConsumePacket());
                                conversation.IncomingSequenceNumber = 0;
                            }
                        }
                        else if (conversation.IncomingSequenceNumber > header.seqNum)
                        {
                            logger.Warn($"Received out of order packet with sn {header.seqNum}");

                            conversation.AckHandler.SendNack(header.seqNum, conversation.LastEndPoint);
                        }
                        else
                        {
                            logger.Warn($"Received a repeat packet that has already been processed with sn {header.seqNum}. Ignoring.");
                        }

                        break;
                    case Shared.Txp.PacketType.ACK:
                        conversation.AckHandler.SpecifyAckReceived();
                        break;
                    case Shared.Txp.PacketType.NACK:
                        conversation.AckHandler.SpecifyNackReceived();
                        break;
                }
            }
        }
        private List<Tuple<uint, byte[]>> SerializeData(byte[] data, TxpClientConversation conversation)
        {
            return Shared.Txp.Interface.SerializeData(data, conversation.ConversationId, ref conversation.OutgoingSequenceNumber);
        }

        private Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final, TxpClientConversation conversation)
        {
            return Shared.Txp.Interface.CreatePacket(rawData, final, conversation.ConversationId, ref conversation.OutgoingSequenceNumber);
        }
    }
}
