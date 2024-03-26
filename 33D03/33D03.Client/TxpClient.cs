using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared;
using System.Runtime.InteropServices;
using Microsoft.VisualBasic;

namespace _33D03.Client
{
    // Delegate for handling received packets.
    public delegate void PacketReceived(byte[] data);

    public class TxpClient
    {
        // Logger instance for logging messages.
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        // UDP client for sending and receiving data.
        private UdpClient client;
        // Server endpoint to send data to and receive data from.
        private IPEndPoint serverEndPoint;

        // Sequence number for outgoing packets.
        private uint outgoingSequenceNumber = 0;
        // Expected sequence number for incoming packets.
        private uint incomingSequenceNumber = 0;

        // A unique identifier for the conversation between this client and the server.
        private uint conversationId = 0;

        // Handles acknowledging received packets.
        private Shared.Txp.AckHandler ackHandler;

        // A separate thread for listening to incoming data.
        private Thread listenThread;

        // Buffers packets for reassembly.
        private Shared.Txp.PacketBufferer packetBufferer;

        // Event triggered upon receiving a complete packet.
        public event PacketReceived OnPacketReceived;

        // Constructor: initializes client, server endpoint, conversation ID, and starts listening thread.
        public TxpClient(string serverIp, int serverPort)
        {
            // Initialize the UDP client to bind to any available port.
            client = new UdpClient(0);
            // Parse the server IP and port into an IPEndPoint.
            serverEndPoint = new IPEndPoint(IPAddress.Parse(serverIp), serverPort);
            // Generate a random conversation ID.
            conversationId = (uint)new Random(DateTime.Now.Millisecond).Next(); // Better randomness needed.

            // Initialize the ack handler with the client and conversation ID.
            ackHandler = new Shared.Txp.AckHandler(client, conversationId);

            // Initialize the packet bufferer for handling packet fragments.
            packetBufferer = new Shared.Txp.PacketBufferer();

            // Set up the listening thread.
            listenThread = new Thread(ListenForData);
        }

        // Starts the listening thread for incoming data.
        public void Start()
        {
            listenThread.Start();
        }
        
        // Sends data to the server, with a specified number of retry attempts.
        public void Send(byte[] data, int attempts = 3)
        {
            // If out of attempts, throw an exception.
            if (attempts == 0)
            {
                throw new Exception("Failed to send data after 3 attempts");
            }

            // Serialize the data into packets ready for sending.
            var packetsToQueue = SerializeData(data);

            // Loop through each packet, sending and handling ACKs/NACKs.
            foreach (var packet in packetsToQueue)
            {
                // Log the packet sequence number being sent.
                logger.Debug($"Sending packet with sn {packet.Item1}");

                // Send the packet to the server.
                client.Send(packet.Item2, packet.Item2.Length, serverEndPoint);

                // Wait for an ACK or a timeout. If a NACK is received, resend.
                if (ackHandler.WaitForAckOrTimeout() == Shared.Txp.AckAction.Rebroadcast)
                {
                    // If a NACK is received, resend the data with one less attempt.
                    Send(data, attempts - 1);
                }
            }

            // Reset the outgoing sequence number after successfully sending the data.
            outgoingSequenceNumber = 0;
        }

        // Listens for incoming data from the server, processing each packet received.
        private void ListenForData()
        {
            while (true) // Infinite loop to continuously listen for data.
            {
                // Block and wait to receive data from the server.
                byte[] receivedData = client.Receive(ref serverEndPoint);
                // If the data received is smaller than the minimum header size, it's invalid.
                if (receivedData.Length < Shared.Txp.Constants.HEADER_SIZE)
                {
                    throw new Exception("Received data is too small to be a packet");
                }

                // Deserialize the header from the received data.
                Shared.Txp.Header header = Shared.Txp.Header.FromBytes(receivedData);
                // Check if the packet is valid based on the header info.
                if (!header.IsValid(receivedData))
                {
                    // Log a warning if the packet is invalid.
                    logger.Warn($"Packet received from server is invalid (magic {header.magic:X}, csum {header.checksum:X}), ignoring");
                    continue;
                }

                // Process the packet based on its type.
                switch (header.type)
                {

                    // Case when the packet type is Data.
                    case Shared.Txp.PacketType.Data:
                        // Log receipt of a data packet.
                        logger.Debug($"Received data packet with sn {header.seqNum}");

                        // Calculate the length of the actual data received by subtracting the header size.
                        var lengthOfDataReceived = receivedData.Length - Shared.Txp.Constants.HEADER_SIZE;

                        // If the sequence number matches the expected incoming sequence number...
                        if (incomingSequenceNumber == header.seqNum)
                        {
                            // Add the packet's data to the buffer for reassembly.
                            packetBufferer.AddPacket(header.GetContainedData(receivedData));
                            // Increment expected incoming sequence number for the next packet.
                            incomingSequenceNumber++;

                            // Acknowledge receipt of the packet.
                            ackHandler.SendAck(header.seqNum, serverEndPoint);

                            // If this packet is marked as the final packet in a message...
                            if (header.finish == 1)
                            {
                                // Raise the OnPacketReceived event with the assembled message.
                                OnPacketReceived(packetBufferer.ConsumePacket());
                                // Reset the incoming sequence number for a new message.
                                incomingSequenceNumber = 0;
                            }
                        }
                        // If the received packet's sequence number is less than expected, it's out of order.
                        else if (incomingSequenceNumber > header.seqNum)
                        {
                            logger.Warn($"Received out of order packet with sn {header.seqNum}");
                            // Send a NACK in response to request retransmission.
                            ackHandler.SendNack(header.seqNum, serverEndPoint);
                        }
                        else
                        {
                            // Log receipt of a repeated packet.
                            logger.Warn($"Received a repeat packet that has already been processed with sn {header.seqNum}. Ignoring.");
                        }
                        break;
                    // Case when the packet type is ACK (Acknowledgement).
                    case Shared.Txp.PacketType.ACK:
                        // Notify the AckHandler that an ACK was received.
                        ackHandler.SpecifyAckReceived();
                        break;
                    // Case when the packet type is NACK (Negative Acknowledgement).
                    case Shared.Txp.PacketType.NACK:
                        // Notify the AckHandler that a NACK was received.
                        ackHandler.SpecifyNackReceived();
                        break;
                }
            }
        }

        // Serializes the data into packets, each with a sequence number and potentially other metadata.
        private List<Tuple<uint, byte[]>> SerializeData(byte[] data)
        {
            // Call the static method to serialize the data, providing the conversationId and reference to outgoingSequenceNumber.
            return Shared.Txp.Interface.SerializeData(data, conversationId, ref outgoingSequenceNumber);
        }

        // Creates a single packet from the raw data, marking it as final or not.
        private Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final)
        {
            // Call the static method to create a single packet from the raw data.
            return Shared.Txp.Interface.CreatePacket(rawData, final, conversationId, ref outgoingSequenceNumber);
        }
    }
}