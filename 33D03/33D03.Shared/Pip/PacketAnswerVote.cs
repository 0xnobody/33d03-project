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

    public PacketAnswerVote(Header constructheader, Guid constructvoteGuid, ushort constructResponse)       //constructor
        {
        header = constructheader;
        voteId = constructvoteGuid;
        response= constructResponse;
        }

        public Header HeaderInfo{
        get { return header; }
        }

        public ushort GetResponse(){
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
