using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    public struct PacketBroadcastVote
    {
        Header header;
        Guid voteGuid;
        uint questionLength;
        // Question - voteLength UTF-8 bytes

        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }
        public static PacketBroadcastVote FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<PacketBroadcastVote>(data);
        }
        public byte[] Serialize(string vote)
        {
            var voteBytes = Encoding.UTF8.GetBytes(vote);
            if (voteBytes.Length != questionLength)
            {
                throw new ArgumentException("Vote length does not match provided vote");
            }

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + questionLength];
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this));
            Buffer.BlockCopy(voteBytes, 0, completedPacketBytes, Marshal.SizeOf(header), (int)questionLength);

            return completedPacketBytes;
        }
        public string GetQuestion(byte[] fullPacketData)
        {
            return Encoding.UTF8.GetString(fullPacketData, Marshal.SizeOf(header), (int)voteLength);
        }
    }
}
