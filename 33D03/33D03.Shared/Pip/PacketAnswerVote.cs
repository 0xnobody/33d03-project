using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    public enum VoteResponse : ushort
    {
        UNSAT = 0,
        SAT = 1,
        UNKNOWN = 2
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 36)]
    public struct PacketAnswerVote
    {
        public Header header;
        public Guid voteId;
        public VoteResponse response;

        public PacketAnswerVote(Header constructheader, Guid constructvoteGuid, VoteResponse constructResponse)       //constructor
        {
            header = constructheader;
            voteId = constructvoteGuid;
            response = constructResponse;
        }


        public Header HeaderInfo
        {
            get { return header; }
        }

        public Guid GetGuid()
        {
            return voteId;
        }

        public VoteResponse GetResponse()
        {
            return response;
        }

        public byte[] ToBytes()                 //struct to bytes 
        {
            return Serialization.StructureToByteArray(this);
        }

        public static PacketAnswerVote FromBytes(byte[] data)       //server side byte to struct for votes
        {
            return Serialization.ByteArrayToStructure<PacketAnswerVote>(data);
        }

        public byte[] Serialize()               //serializes struct
        {
            return ToBytes();
        }
    }
}
