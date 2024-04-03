using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using System.IO.Hashing;

namespace _33D03.Shared.Txp
{
    public enum PacketType : ushort
    {
        /// <summary>
        /// Packet contains data segment immediately following the header
        /// </summary>
        Data = 0,

        /// <summary>
        /// Packet contains an acknowledgment
        /// </summary>
        ACK = 1,

        /// <summary>
        /// Packet contains a negative acknowledgement
        /// </summary>
        NACK = 2,

        /// <summary>
        /// Packet contains a synchronization request - If the client doesn't respond with a SYN-ACK, 
        /// the server will resend the SYN packet up to a maximum number of times.
        /// If the server doesn't receive a SYN-ACK after the maximum number of attempts, the conversation ID is purged.
        /// </summary>
        SYN = 3,

        /// <summary>
        /// Response to a synchronization request - The client must respond with a SYN-ACK
        /// </summary>
        SYN_ACK = 5,

        /// <summary>
        /// Packet contains a reset request - The provided conversation ID is purged.
        /// This is just a hint. Does not need to be acknowledged.
        /// </summary>
        RESET = 6,
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 24)]
    public struct Header
    {
        public uint magic;
        public uint checksum;
        public uint convId;
        public uint pcktNum;
        public uint seqNum;
        public ushort finish;
        public PacketType type;

        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

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

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + contents.Length];
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this));
            Buffer.BlockCopy(contents, 0, completedPacketBytes, Marshal.SizeOf(this), contents.Length);

            var calculatedChecksum = CalculateChecksum(completedPacketBytes);

            // Set calculatedChecksum at offset 4 of the byte array, which corresponds to the checksum field in the struct
            // This saves us from copying the entire struct back into the byte array
            int checksumOffset = (int)Marshal.OffsetOf<Header>("checksum");
            Buffer.BlockCopy(Serialization.GetBytes(calculatedChecksum), 0, completedPacketBytes, checksumOffset, sizeof(uint));

            return completedPacketBytes;
        }

        /// <summary>
        /// Determines if the magic and checksum of the packet is correct
        /// </summary>
        /// <param name="rawFullPacketBytes">Corresponds to the bytes ENTIRE packet, including the header and data (if any)</param>
        /// <returns>True if valid, false otherwise</returns>
        public bool IsValid(byte[] rawFullPacketBytes)
        {
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

            return CalculateChecksum(rawFullPacketBytes) == checksum;
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

        public uint CalculateChecksum(byte[] rawFullPacketBytes)
        {
            var hashBeginIndex = (int)Marshal.OffsetOf<Header>("convId");

            var hashData = new byte[rawFullPacketBytes.Length - hashBeginIndex];
            Buffer.BlockCopy(rawFullPacketBytes, hashBeginIndex, hashData, 0, hashData.Length);

            var csum = Crc32.HashToUInt32(hashData);

            logger.Trace($"Calculated checksum {csum:X} for bytes: {BitConverter.ToString(hashData)}");

            return csum;
        }
    }
}
