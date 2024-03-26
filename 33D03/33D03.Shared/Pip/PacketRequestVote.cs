using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 20)]
    public struct PacketRequestVote
    {
        Header header;
        Guid voteGuid;
        uint questionLength;
        // Question - questionLength UTF-8 bytes


        public PacketRequestVote(Header constructheader, Guid constructvoteGuid, uint constructquestionLength)
        {
        header = constructheader;
        voteGuid = constructvoteGuid;
        questionLength = constructquestionLength;
        }
        
        public byte[] ToBytes()
        {
            return Serialization.StructureToByteArray(this);
        }

        public static PacketRequestVote FromBytes(byte[] data)
        {
            return Serialization.ByteArrayToStructure<PacketRequestVote>(data);
        }

        public byte[] Serialize(string question)
        {
            var questionBytes = Encoding.UTF8.GetBytes(question);
            if (questionBytes.Length != questionLength)
            {
                throw new ArgumentException("Question length does not match provided question");
            }

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + questionLength];
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this));
            Buffer.BlockCopy(questionBytes, 0, completedPacketBytes, Marshal.SizeOf(header), (int)questionLength);

            return completedPacketBytes;
        }

        public string GetQuestion(byte[] fullPacketData)
        {
            return Encoding.UTF8.GetString(fullPacketData, Marshal.SizeOf(header), (int)questionLength);
        }
    }
}
