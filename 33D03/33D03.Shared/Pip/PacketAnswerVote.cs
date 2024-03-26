using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    public struct PacketAnswerVote
    {
        Header header;
        Guid voteId;
        ushort response;

        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }

        public static PacketAnswerVote FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<PacketAnswerVote>(data);
        }

        public byte[] Serialize()
        {
            return ToBytes();
        }
    }
}
