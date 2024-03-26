using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public static class Interface
    {
        public static List<Tuple<uint, byte[]>> SerializeData(byte[] data, uint conversationId, ref uint sequenceNum)
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

            List<Tuple<uint, byte[]>> outgoingPackets = new List<Tuple<uint, byte[]>>();

            for (int i = 0; i < chunks.Count; i++)
            {
                outgoingPackets.Add(CreatePacket(chunks[i], i == chunks.Count - 1, conversationId, ref sequenceNum));
            }

            return outgoingPackets;
        }

        public static Tuple<uint, byte[]> CreatePacket(byte[] rawData, bool final, uint conversationId, ref uint sequenceNum)
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
                finish = final ? (ushort)1 : (ushort)0,
                type = Shared.Txp.PacketType.Data
            };

            byte[] packetBytes = header.Serialize(rawData);

            return new Tuple<uint, byte[]>(header.seqNum, packetBytes);
        }
    }
}
