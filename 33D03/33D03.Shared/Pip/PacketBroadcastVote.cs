using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Dynamic;
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    public struct ServerVoteId{
        public Guid voteid;
        public string question;
        public int vote_counter;
        public int sat_counter;
        public int unsat_counter;
        public int timeout_counter;

        public ServerVoteId(Guid id, string qustn){
            voteid = id;
            question = qustn;
            vote_counter = 0;
            sat_counter = 0;
            unsat_counter = 0;
            timeout_counter = 0;
        }

        public static void AddVoteToList(List<ServerVoteId> voteList, Guid voteid, string question){
            voteList.Add(new ServerVoteId(voteid, question));
        }
        public static void DeleteVoteFromList(){

        }
    }



    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 22)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct PacketBroadcastVote // Declaring a public structure named PacketBroadcastVote.
    {
        Header header; // Declaring a field of type Header.
        Guid voteGuid; // Declaring a field of type Guid.
        uint questionLength; // Declaring a field of type uint.

        public Header HeaderInfo
        {
            get { return header; }
        }

        public PacketBroadcastVote(Header hder, Guid guid, uint QuestionLength)
        {
            header = hder;
            voteGuid = guid;
            questionLength = QuestionLength;
        }

        public Guid GetGuid()
        {
            return voteGuid;
        }

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static PacketBroadcastVote FromBytes(byte[] data) // Defining a static method to create a PacketBroadcastVote struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<PacketBroadcastVote>(data); // Returning a PacketBroadcastVote struct created from the byte array.
        }

        public byte[] Serialize(string question)
        {
            var questionBytes = Encoding.UTF8.GetBytes(question);
            questionLength = (uint)questionBytes.Length;
            int totalSize = Marshal.SizeOf(typeof(PacketBroadcastVote)) + questionBytes.Length;
            var completedPacketBytes = new byte[totalSize];
            byte[] structBytes = ToBytes();
            Buffer.BlockCopy(structBytes, 0, completedPacketBytes, 0, structBytes.Length);
            Buffer.BlockCopy(questionBytes, 0, completedPacketBytes, structBytes.Length, questionBytes.Length);

            return completedPacketBytes;
        }



        public static (PacketBroadcastVote, string) Deserialize(byte[] data)
        {
            // Extract the PacketRequestVote structure
            int sizeOfPacketBroadcastVote = Marshal.SizeOf(typeof(PacketBroadcastVote));
            IntPtr ptr = Marshal.AllocHGlobal(sizeOfPacketBroadcastVote);
            try
            {
                Marshal.Copy(data, 0, ptr, sizeOfPacketBroadcastVote);
                PacketBroadcastVote packetBroadcastVote = (PacketBroadcastVote)Marshal.PtrToStructure(ptr, typeof(PacketBroadcastVote));

                // Calculate the start index and length of the question string
                int questionStartIndex = sizeOfPacketBroadcastVote;
                int questionLength = data.Length - questionStartIndex; // Assuming the rest of the array is the question

                // Extract the question string
                string question = Encoding.UTF8.GetString(data, questionStartIndex, questionLength);

                return (packetBroadcastVote, question);
            }
            finally
            {
                Marshal.FreeHGlobal(ptr);
            }
        }

        public string GetQuestion(byte[] fullPacketData) // Defining a method to extract the vote string from a serialized PacketBroadcastVote.
        {
            return Encoding.UTF8.GetString(fullPacketData, Marshal.SizeOf(header), (int)questionLength); // Returning the vote string extracted from the byte array.
        }

    }
}
