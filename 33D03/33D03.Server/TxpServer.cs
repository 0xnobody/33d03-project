using System;
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

namespace _33D03.Server
{
    delegate void PacketReceived(TxpClientConversation clientConversation, byte[] data);

    // Manages conversation state with a client, including sequence numbers and the last known endpoint.
    internal class TxpClientConversation
    {
        // Unique identifier for the conversation.
        public uint ConversationId;
        // The last known endpoint from which the client sent a packet.
        public IPEndPoint LastEndPoint;

        public SegmentHandler SegmentHandler;

        // Initializes a new conversation with a client.
        public TxpClientConversation(UdpClient client, uint conversationId, IPEndPoint initialEndPoint)
        {
            ConversationId = conversationId;
            LastEndPoint = initialEndPoint; // Store the client's endpoint.
            SegmentHandler = new SegmentHandler(client, conversationId);
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

        // Event triggered when a complete data packet is received.
        public event PacketReceived OnPacketReceived;

        // Initializes the server to listen on the specified port.
        public TxpServer(int port)
        {
            server = new UdpClient(port); // Bind the server to the specified port.
        }

        // Starts the server's listening thread, beginning packet reception.
        public void Start()
        {
            while (true)
            {
                ListenForData();
            }
        }

        // Sends data to the specified client conversation. Attempts parameter defines the max number of send attempts.
        public void Send(byte[] data, TxpClientConversation conversation)
        {
            conversation.SegmentHandler.SendOrQueuePacket(data, conversation.LastEndPoint);
        }

        private void ListenForData()
        {
            IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Loopback, 0000);

            var pckt = Shared.Txp.Interface.ListenForPacket(server, ref remoteEndPoint);
            if (pckt == null)
            {
                logger.Warn("Something went wrong in listening for data");
                throw new Exception("Received null response from ListenForPacket");
            }

            var header = pckt.Item1;
            var receivedData = pckt.Item2;

            // If this is the first packet from a new conversation, create a new conversation object.
            if (!conversations.ContainsKey(header.convId))
            {
                conversations.Add(header.convId, new TxpClientConversation(server, header.convId, remoteEndPoint));
            }

            // Retrieve the conversation object associated with this packet.
            var conversation = conversations[header.convId];

            // Update the conversation's last known endpoint. This is important if the client's network address changes.
            conversation.LastEndPoint = remoteEndPoint;

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
                default:
                    logger.Warn("Received unknown packet type");
                    break;
            }
        }
    }
}
