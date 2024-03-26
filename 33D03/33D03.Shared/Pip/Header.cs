using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    public enum PacketType : ushort
    {
        Hello_C2S = 0x0000,
        Hello_S2C = 0x0001,
        Vote_Request_Vote_C2S = 0x0002,
        Vote_Broadcast_Vote_S2C = 0x0003,
        Vote_Answer_Vote_C2S = 0x0004,
        Vote_Broadcast_Vote_Result_S2C = 0x0005,
    }
    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    public struct Header
    {
        public uint magic;
        public uint checksum;
        public PacketType type;

        public Header(PacketType pcktType)
        {
            magic = Constants.MAGIC;
            checksum = 0;
            type = pcktType;
        }

        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }

        public static Header FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<Header>(data);
        }

        public byte[] Serialize()
        {
            return ToBytes();
        }
    }
}
