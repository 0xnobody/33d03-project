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
    public delegate void PacketReceived(byte[] data);
    public class TxpClient
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private UdpClient client;
        private IPEndPoint serverEndPoint;

        private uint outgoingSequenceNumber = 0;
        private uint incomingSequenceNumber = 0;

        private uint conversationId = 0;

        private Shared.Txp.AckHandler ackHandler;

        private Thread listenThread;

        private Shared.Txp.PacketBufferer packetBufferer;

        public event PacketReceived OnPacketReceived;

        public TxpClient(string serverIp, int serverPort)
        {
            client = new UdpClient(0); // Passing 0 to bind to any available port
            serverEndPoint = new IPEndPoint(IPAddress.Parse(serverIp), serverPort);
            conversationId = (uint)new Random(DateTime.Now.Millisecond).Next(); // TODO: better random generation

            ackHandler = new Shared.Txp.AckHandler(client, conversationId);

            packetBufferer = new Shared.Txp.PacketBufferer();

            listenThread = new Thread(ListenForData);
        }

        public void Start()
        {
            listenThread.Start();
        }
        
        public void Send(byte[] data, int attempts = 3)
        {
            if (attempts == 0)
            {
                throw new Exception("Failed to send data after 3 attempts");
            }

            var packetsToQueue = SerializeData(data);

            foreach (var packet in packetsToQueue)
            {
                logger.Debug($"Sending packet with sn {packet.Item1}");

                client.Send(packet.Item2, packet.Item2.Length, serverEndPoint);

                // Wait for the ACK/NACK for a certain timeout
                if (ackHandler.WaitForAckOrTimeout() == Shared.Txp.AckAction.Rebroadcast)
                {
                    // Resend packet, decrease attempt number
                    Send(data, attempts - 1);
                }
            }

            // Reset outgoing sn after full packet is sent.
            outgoingSequenceNumber = 0;
        }

        private void ListenForData()
        {
            while (true)
            {
                byte[] receivedData = client.Receive(ref serverEndPoint);
                if (receivedData.Length < Shared.Txp.Constants.HEADER_SIZE)
                {
                    throw new Exception("Received data is too small to be a packet");
                }

                Shared.Txp.Header header = Shared.Txp.Header.FromBytes(receivedData);
                if (!header.IsValid(receivedData))
                {
                    logger.Warn($"Packet received from server is invalid (magic {header.magic:X}, csum {header.checksum:X}), ignoring");

                    //
                    // We can't send a NACK here, as the convId may also be invalid.
                    // So we just wait for a retransmission.
                    //

                    continue;
                }

                switch (header.type)
                {
                    case Shared.Txp.PacketType.Data:
                        logger.Debug($"Received data packet with sn {header.seqNum}");

                        var lengthOfDataReceived = receivedData.Length - Shared.Txp.Constants.HEADER_SIZE;

                        if (incomingSequenceNumber == header.seqNum)
                        {
                            packetBufferer.AddPacket(header.GetContainedData(receivedData));
                            incomingSequenceNumber++;

                            // logger.Trace($"Current buffer state: {BitConverter.ToString(packetBuffer)}");

                            ackHandler.SendAck(header.seqNum, serverEndPoint);

                            if (header.finish == 1)
                            {
                                OnPacketReceived(packetBufferer.ConsumePacket());
                                incomingSequenceNumber = 0;
                            }
                        }
                        else if (incomingSequenceNumber > header.seqNum)
                        {
                            logger.Warn($"Received out of order packet with sn {header.seqNum}");

                            ackHandler.SendNack(header.seqNum, serverEndPoint);
                        }
                        else
                        {
                            logger.Warn($"Received a repeat packet that has already been processed with sn {header.seqNum}. Ignoring.");
                        }
                        break;
                    case Shared.Txp.PacketType.ACK:
                        ackHandler.SpecifyAckReceived();
                        break;
                    case Shared.Txp.PacketType.NACK:
                        ackHandler.SpecifyNackReceived();
                        break;
                }
            }
        }

        private List<Tuple<uint, byte[]>> SerializeData(byte[] data)
        {
            return Shared.Txp.Interface.SerializeData(data, conversationId, ref outgoingSequenceNumber);
        }

        private Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final)
        {
            return Shared.Txp.Interface.CreatePacket(rawData, final, conversationId, ref outgoingSequenceNumber);
        }
    }
}
