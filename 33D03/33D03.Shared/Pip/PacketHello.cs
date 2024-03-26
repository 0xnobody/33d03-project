using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    public enum Feature : ushort
    {
        SMTVerificationFeature = 0,
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 20)]
    public struct PacketHello
    {
        Header header;
        uint version;
        ushort numFeatures;
        // Features - 2 bytes each

        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }
        public static Header FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<Header>(data);
        }

        public byte[] Serialize(Feature[] features)
        {
            if (features.Length != numFeatures)
            {
                throw new ArgumentException("Incorrect number of features");
            }

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + numFeatures * 2];
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this));
            for (int i = 0; i < numFeatures; i++)
            {
                Buffer.BlockCopy(BitConverter.GetBytes((ushort)features[i]), 0, completedPacketBytes, Marshal.SizeOf(header) + i * 2, 2);
            }

            return completedPacketBytes;
        }

        public Feature[] GetFeatures(byte[] fullPacketData)
        {
            Feature[] features = new Feature[numFeatures];
            for (int i = 0; i < numFeatures; i++)
            {
                features[i] = (Feature)BitConverter.ToUInt16(fullPacketData, Marshal.SizeOf(header) + i * 2);
            }
            return features;
        }
    }
}
