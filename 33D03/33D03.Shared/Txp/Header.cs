using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public enum PacketType : ushort
    {
        Data = 0,
        ACK = 1,
        NACK = 2,
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 20)]
    public struct Header
    {
        public uint magic;
        public uint checksum;
        public uint convId;
        public uint seqNum;
        public ushort finish;
        public PacketType type;

        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }

        /// <summary>
        /// Serializes the header into a byte array, and calculates the correct checksum.
        /// </summary>
        /// <returns>The byte array representing the packet header</returns>
        public byte[] Serialize(byte[] contents)
        {
            if (contents.Length > Constants.DATA_SIZE)
            {
                throw new ArgumentException("Data too large to fit in a packet");
            }

            if (contents.Length == 0 && type == PacketType.Data)
            {
                throw new ArgumentException("Data must be provided for a data packet");
            }

            if (contents.Length != 0 && type != PacketType.Data)
            {
                throw new ArgumentException("Data must not be provided for a non-data packet");
            }

            checksum = 0;

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + contents.Length];
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this));
            Buffer.BlockCopy(contents, 0, completedPacketBytes, Marshal.SizeOf(this), contents.Length);

            var calculatedChecksum = Checksum.Calculate(completedPacketBytes);

            // Set calculatedChecksum at offset 4 of the byte array, which corresponds to the checksum field in the struct
            // This saves us from copying the entire struct back into the byte array
            int checksumOffset = (int)Marshal.OffsetOf<Header>("checksum");
            Buffer.BlockCopy(BitConverter.GetBytes(calculatedChecksum), 0, completedPacketBytes, checksumOffset, sizeof(uint));

            return completedPacketBytes;
        }

        /// <summary>
        /// Determines if the magic and checksum of the packet is correct
        /// </summary>
        /// <param name="rawFullPacketBytes">Corresponds to the bytes ENTIRE packet, including the header and data (if any)</param>
        /// <returns>True if valid, false otherwise</returns>
        public bool IsValid(byte[] rawFullPacketBytes)
        {
            // We must copy the bytes to a new array, as the checksum field is set to 0 in the struct
            // TODO: Perhaps we can avoid copying by specifying in the checksum calculation to ignore the checksum field

            if (magic != Constants.MAGIC)
            {
                return false;
            }

            // Checksum is only valid for data packets
            // TODO: Perhaps we should also include / verify the checksum for ACK and NACK packets?
            if (type != PacketType.Data)
            {
                return true;
            }

            var rawFullPacketBytesChecksumZero = new byte[rawFullPacketBytes.Length];
            Buffer.BlockCopy(rawFullPacketBytes, 0, rawFullPacketBytesChecksumZero, 0, rawFullPacketBytes.Length);

            int checksumOffset = (int)Marshal.OffsetOf<Header>("checksum");
            Buffer.BlockCopy(BitConverter.GetBytes(0ul), 0, rawFullPacketBytesChecksumZero, checksumOffset, sizeof(uint));

            return Checksum.Calculate(rawFullPacketBytesChecksumZero) == checksum;
        }
        public static Header FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<Header>(data);
        }

        public byte[] GetContainedData(byte[] rawFullPacketBytes)
        {
            if (type != PacketType.Data)
            {
                throw new InvalidOperationException("Packet does not contain data");
            }

            var containedDataBytes = new byte[rawFullPacketBytes.Length - Marshal.SizeOf(this)];
            Buffer.BlockCopy(rawFullPacketBytes, Marshal.SizeOf(this), containedDataBytes, 0, containedDataBytes.Length);

            return containedDataBytes;
        }
    }
}
