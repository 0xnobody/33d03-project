using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 36)]
    public struct PacketAnswerVote
    {
        Header header;
        Guid voteId;
        Guid newguid;
        ushort response;

        public PacketAnswerVote(Header constructheader, Guid constructvoteGuid, Guid NewGuid, ushort constructResponse)       //constructor
        {
            header = constructheader;
            voteId = constructvoteGuid;
            newguid = NewGuid;
            response = constructResponse;
        }


        public Guid GetNewGuid(){
            return newguid;
        }
        public Header HeaderInfo
        {
            get { return header; }
        }

        public Guid GetGuid()
        {
            return voteId;
        }

        public ushort GetResponse()
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
