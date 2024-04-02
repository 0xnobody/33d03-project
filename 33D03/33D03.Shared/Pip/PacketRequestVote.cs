using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Security.Cryptography.X509Certificates;
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 22)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct PacketRequestVote // Declaring a public structure named PacketRequestVote.
    {
        Header header; // Declaring a field of type Header.
        Guid voteGuid; // Declaring a field of type Guid.
        uint questionLength; // Declaring a field of type uint.

        public Header HeaderInfo
        {
            get { return header; }
        }

        public PacketRequestVote(Header constructheader, Guid constructvoteGuid, uint constructquestionLength) // Defining a constructor for the struct.
        {
            header = constructheader; // Assigning the value of the parameter constructheader to the field header.
            voteGuid = constructvoteGuid; // Assigning the value of the parameter constructvoteGuid to the field voteGuid.
            questionLength = constructquestionLength; // Assigning the value of the parameter constructquestionLength to the field questionLength.
        }

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static PacketRequestVote FromBytes(byte[] data) // Defining a static method to create a PacketRequestVote struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<PacketRequestVote>(data); // Returning a PacketRequestVote struct created from the byte array.
        }

        public byte[] Serialize(string question)
        {
            var questionBytes = Encoding.UTF8.GetBytes(question);
            questionLength = (uint)questionBytes.Length;
            int totalSize = Marshal.SizeOf(typeof(PacketRequestVote)) + questionBytes.Length;
            var completedPacketBytes = new byte[totalSize];
            byte[] structBytes = ToBytes();
            Buffer.BlockCopy(structBytes, 0, completedPacketBytes, 0, structBytes.Length);
            Buffer.BlockCopy(questionBytes, 0, completedPacketBytes, structBytes.Length, questionBytes.Length);

            return completedPacketBytes;
        }

        public static (PacketRequestVote, string) Deserialize(byte[] data)
        {
            // Extract the PacketRequestVote structure
            int sizeOfPacketRequestVote = Marshal.SizeOf(typeof(PacketRequestVote));
            IntPtr ptr = Marshal.AllocHGlobal(sizeOfPacketRequestVote);
            try
            {
                Marshal.Copy(data, 0, ptr, sizeOfPacketRequestVote);
                PacketRequestVote packetRequestVote = (PacketRequestVote)Marshal.PtrToStructure(ptr, typeof(PacketRequestVote));

                // Calculate the start index and length of the question string
                int questionStartIndex = sizeOfPacketRequestVote;
                int questionLength = data.Length - questionStartIndex; // Assuming the rest of the array is the question

                // Extract the question string
                string question = Encoding.UTF8.GetString(data, questionStartIndex, questionLength);

                return (packetRequestVote, question);
            }
            finally
            {
                Marshal.FreeHGlobal(ptr);
            }
        }

        public string GetQuestion(byte[] fullPacketData) // Defining a method to extract the question string from a serialized PacketRequestVote.
        {
            return Encoding.UTF8.GetString(fullPacketData, Marshal.SizeOf(header), (int)questionLength); // Returning the question string extracted from the byte array.
        }

        public string GetLength()
        {
            return questionLength.ToString();
        }
        public Guid Getguid()
        {
            return voteGuid;
        }
    }

}
