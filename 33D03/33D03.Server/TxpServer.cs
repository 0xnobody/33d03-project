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

namespace _33D03.Server
{
    delegate void PacketReceived(TxpClientConversation clientConversation, byte[] data);

    // Manages conversation state with a client, including sequence numbers and the last known endpoint.
    internal class TxpClientConversation
    {
        // Unique identifier for the conversation.
        public uint ConversationId;
        // Sequence number for the next expected incoming packet.
        public uint IncomingSequenceNumber;
        // Sequence number for the next outgoing packet.
        public uint OutgoingSequenceNumber;
        // The last known endpoint from which the client sent a packet.
        public IPEndPoint LastEndPoint;

        // Handles acknowledging received packets.
        public Shared.Txp.AckHandler AckHandler;
        // Buffers and reassembles incoming packet data.
        public Shared.Txp.PacketBufferer PacketBufferer;

        // Initializes a new conversation with a client.
        public TxpClientConversation(UdpClient client, uint conversationId, IPEndPoint initialEndPoint)
        {
            ConversationId = conversationId;
            IncomingSequenceNumber = 0; // Start at zero, expecting the first packet to also be numbered zero.
            OutgoingSequenceNumber = 0; // Start at zero for the first packet this server will send.
            LastEndPoint = initialEndPoint; // Store the client's endpoint.

            // Initialize the AckHandler and PacketBufferer for this conversation.
            AckHandler = new Shared.Txp.AckHandler(client, conversationId);
            PacketBufferer = new Shared.Txp.PacketBufferer();
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

        // Thread for listening to incoming packets.
        private Thread listenerThread;

        // Event triggered when a complete data packet is received.
        public event PacketReceived OnPacketReceived;

        // Initializes the server to listen on the specified port.
        public TxpServer(int port)
        {
            server = new UdpClient(port); // Bind the server to the specified port.
            listenerThread = new Thread(ListenForData); // Set up the listening thread.
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
        public void Send(byte[] data, TxpClientConversation conversation, int attempts = 3)
        {
            if (attempts == 0)
            {
                // If all attempts to send are exhausted, throw an exception.
                throw new Exception("Failed to send data after 3 attempts");
            }

            // Serialize the data into packets for sending.
            var packetsToQueue = SerializeData(data, conversation);

            foreach (var packet in packetsToQueue)
            {
                // Log the attempt to send a packet.
                logger.Debug($"Sending packet to cid {conversation.ConversationId} at {conversation.LastEndPoint} with sn {packet.Item1}");

                // Send the packet to the client's last known endpoint.
                server.Send(packet.Item2, packet.Item2.Length, conversation.LastEndPoint);

                // If an ACK isn't received before timeout, log a warning and attempt to resend.
                if (ListenForAck(ref conversation.LastEndPoint) == Shared.Txp.AckType.Nack)
                {
                    logger.Warn($"Timeout passed for sn {packet.Item1}, resending");
                    Send(data, conversation, attempts - 1); // Resend with one less attempt.
                }
            }

            // Reset the outgoing sequence number after the entire message has been sent.
            conversation.OutgoingSequenceNumber = 0;
        }

        private byte[]? ReceiveWithTimeout(ref IPEndPoint remoteEndPoint, TimeSpan timeout)
        {
            var asyncResult = server.BeginReceive(null, null);
            asyncResult.AsyncWaitHandle.WaitOne(timeout);
            if (asyncResult.IsCompleted)
            {
                IPEndPoint remoteEP = null;
                byte[] receivedData = server.EndReceive(asyncResult, ref remoteEP);

                return receivedData;
            }
            else
            {
                return null;
            }
        }

        private Tuple<Shared.Txp.Header, byte[]>? ListenForPacket(ref IPEndPoint remoteEndPoint, TimeSpan? timeout = null)
        {
            // Block and wait to receive data, storing the sender's endpoint.
            byte[]? receivedData;

            if (timeout == null)
            {
                receivedData = server.Receive(ref remoteEndPoint);
            }
            else
            {
                receivedData = ReceiveWithTimeout(ref remoteEndPoint, timeout ?? TimeSpan.MinValue);
            }

            if (receivedData == null)
            {
                return null;
            }

            // Validate the minimum size of received data to ensure it contains a complete header.
            if (receivedData.Length < Shared.Txp.Constants.HEADER_SIZE)
            {
                logger.Log(NLog.LogLevel.Error, "Received data is too small to be a packet");
                throw new Exception("Received data is too small to be a packet");
            }

            // Deserialize the header from the received data to understand the packet's metadata.
            var header = Shared.Txp.Header.FromBytes(receivedData);
            // Validate the packet using the header information. Invalid packets are ignored.
            if (!header.IsValid(receivedData))
            {
                logger.Warn($"Packet received from {remoteEndPoint} is invalid (magic {header.magic:X}, csum {header.checksum:X})");
                // If the packet is invalid, skip the rest of the loop and wait for the next packet.
                return null;
            }

            // Log a message indicating a valid packet has been received.
            logger.Trace($"Received valid packet from of type {Enum.GetName(typeof(Shared.Txp.PacketType), header.type)}");

            return new Tuple<Shared.Txp.Header, byte[]>(header, receivedData);
        }

        private Shared.Txp.AckType ListenForAck(ref IPEndPoint remoteEndPoint)
        {
            var pckt = ListenForPacket(ref remoteEndPoint, TimeSpan.FromMilliseconds(Shared.Txp.Constants.ACK_TIMEOUT_MS));
            if (pckt == null)
            {
                logger.Warn("Timout occurred");
                return Shared.Txp.AckType.Nack;
            }

            if (pckt.Item1.type == Shared.Txp.PacketType.Data)
            {
                logger.Warn("Received data packet where ACK/NACK was expected");
            }

            if (pckt.Item1.type == Shared.Txp.PacketType.ACK)
            {
                return Shared.Txp.AckType.Ack;
            }

            return Shared.Txp.AckType.Nack;
        }
        private void ListenForData()
        {
            IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Loopback, 0000);

            var pckt = ListenForPacket(ref remoteEndPoint);
            if (pckt == null)
            {
                logger.Warn("Something went wrong in listening for data");
                throw new Exception("Received null response from ListenForPacket");
            }

            if (pckt.Item1.type != Shared.Txp.PacketType.Data)
            {

                logger.Warn("Received non-data packet where data packet was expected");
                throw new Exception("Received non-data packet where data packet was expected");
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

            // Log the receipt of a data packet.
            // logger.Debug($"Received {conversation.ConversationId} data packet with sn {header.seqNum}");

            // Calculate the actual data length by subtracting the header size from the total packet size.
            var lengthOfDataReceived = receivedData.Length - Shared.Txp.Constants.HEADER_SIZE;

            // If the sequence number matches what we're expecting, process the packet.
            if (conversation.IncomingSequenceNumber == header.seqNum)
            {
                // Add the packet's data to the buffer for this conversation.
                conversation.PacketBufferer.AddPacket(header.GetContainedData(receivedData));
                // Increment the expected sequence number for the next packet.
                conversation.IncomingSequenceNumber++;

                // Send an acknowledgment for this packet.
                conversation.AckHandler.SendAck(header.seqNum, conversation.LastEndPoint);

                // If this packet is marked as the final one in a sequence...
                if (header.finish == 1)
                {
                    // Trigger the OnPacketReceived event, passing the reassembled data to event subscribers.
                    OnPacketReceived(conversation, conversation.PacketBufferer.ConsumePacket());
                    // Reset the expected sequence number for the next message.
                    conversation.IncomingSequenceNumber = 0;
                }
            }
            else if (conversation.IncomingSequenceNumber > header.seqNum)
            {
                // If we receive an out-of-order packet, log a warning.
                logger.Warn($"Received out of order packet with sn {header.seqNum}");
                // Send a negative acknowledgment to request retransmission of the correct packet.
                conversation.AckHandler.SendNack(header.seqNum, conversation.LastEndPoint);
            }
            else
            {
                // If we receive a repeated packet, log a warning and ignore it.
                logger.Warn($"Received a repeat packet that has already been processed with sn {header.seqNum}. Ignoring.");
            }
        }

        // Serializes the data into a list of packets, each with a sequence number and possibly additional metadata.
        private List<Tuple<uint, byte[]>> SerializeData(byte[] data, TxpClientConversation conversation)
        {
            // Call a shared method to serialize the data, providing necessary metadata from the conversation.
            return Shared.Txp.Interface.SerializeData(data, conversation.ConversationId, ref conversation.OutgoingSequenceNumber);
        }

        // Helper method to create a single packet from raw data, marking it as final if needed, and incrementing the sequence number.
        private Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final, TxpClientConversation conversation)
        {
            // Create and return a single packet with appropriate metadata.
            return Shared.Txp.Interface.CreatePacket(rawData, final, conversation.ConversationId, ref conversation.OutgoingSequenceNumber);
        }
    }
}
