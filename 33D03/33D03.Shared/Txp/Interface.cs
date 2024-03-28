using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public static class Interface
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        public static Dictionary<uint, byte[]> SerializeData(byte[] data, uint pcktNum, uint conversationId, ref uint sequenceNum)
        {
            var chunkSize = Shared.Txp.Constants.DATA_SIZE;

            // Split data into chunkSize
            List<byte[]> chunks = new List<byte[]>();
            for (int i = 0; i < data.Length; i += chunkSize)
            {
                byte[] chunk = new byte[Math.Min(chunkSize, data.Length - i)];
                Array.Copy(data, i, chunk, 0, chunk.Length);
                chunks.Add(chunk);
            }

            Dictionary<uint, byte[]> outgoingPackets = new Dictionary<uint, byte[]>();

            for (int i = 0; i < chunks.Count; i++)
            {
                var pckt = CreatePacket(chunks[i], pcktNum, i == chunks.Count - 1, conversationId, ref sequenceNum);
                outgoingPackets.Add(pckt.Item1, pckt.Item2);
            }

            return outgoingPackets;
        }

        public static Tuple<uint, byte[]> CreatePacket(byte[] rawData, uint pcktNum, bool final, uint conversationId, ref uint sequenceNum)
        {
            if (rawData.Length > Shared.Txp.Constants.DATA_SIZE)
            {
                throw new Exception("Data too large to fit in a packet");
            }

            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = conversationId,
                seqNum = sequenceNum++,
                pcktNum = pcktNum,
                finish = final ? (ushort)1 : (ushort)0,
                type = Shared.Txp.PacketType.Data
            };

            byte[] packetBytes = header.Serialize(rawData);

            return new Tuple<uint, byte[]>(header.seqNum, packetBytes);
        }

        public static byte[]? ReceiveWithTimeout(UdpClient client, ref IPEndPoint remoteEndPoint, TimeSpan timeout)
        {
            var asyncResult = client.BeginReceive(null, null);
            asyncResult.AsyncWaitHandle.WaitOne(timeout);
            if (asyncResult.IsCompleted)
            {
                IPEndPoint remoteEP = null;
                byte[] receivedData = client.EndReceive(asyncResult, ref remoteEP);

                return receivedData;
            }
            else
            {
                return null;
            }
        }

        public static Tuple<Shared.Txp.Header, byte[]>? ListenForPacket(UdpClient client, ref IPEndPoint remoteEndPoint, TimeSpan? timeout = null)
        {
            // Block and wait to receive data, storing the sender's endpoint.
            byte[]? receivedData;

            if (timeout == null)
            {
                receivedData = client.Receive(ref remoteEndPoint);
            }
            else
            {
                receivedData = ReceiveWithTimeout(client, ref remoteEndPoint, timeout ?? TimeSpan.MinValue);
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

            return new Tuple<Shared.Txp.Header, byte[]>(header, receivedData);
        }
    }
}
