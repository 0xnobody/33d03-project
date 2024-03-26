using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Dynamic;
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    [StructLayout(LayoutKind.Sequential, Pack = 1)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct PacketBroadcastVote // Declaring a public structure named PacketBroadcastVote.
    {
        Header header; // Declaring a field of type Header.
        Guid voteGuid; // Declaring a field of type Guid.
        uint questionLength; // Declaring a field of type uint.

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static PacketBroadcastVote FromBytes(byte[] data) // Defining a static method to create a PacketBroadcastVote struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<PacketBroadcastVote>(data); // Returning a PacketBroadcastVote struct created from the byte array.
        }

        public byte[] Serialize(string vote) // Defining a method to serialize the struct along with a vote string into a byte array.
        {
            var voteBytes = Encoding.UTF8.GetBytes(vote); // Getting the byte array representation of the vote string.
            if (voteBytes.Length != questionLength) // Checking if the length of the vote string matches the expected length.
            {
                throw new ArgumentException("Vote length does not match provided vote"); // Throwing an exception if the lengths do not match.
            }

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + questionLength]; // Creating a byte array to hold the serialized struct and vote string.
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(this)); // Copying the byte array representation of the struct into the completedPacketBytes array.
            Buffer.BlockCopy(voteBytes, 0, completedPacketBytes, Marshal.SizeOf(header), (int)questionLength); // Copying the byte array representation of the vote string into the completedPacketBytes array.

            return completedPacketBytes; // Returning the completed byte array.
        }

        public string GetQuestion(byte[] fullPacketData) // Defining a method to extract the vote string from a serialized PacketBroadcastVote.
        {
            return Encoding.UTF8.GetString(fullPacketData, Marshal.SizeOf(header), (int)questionLength); // Returning the vote string extracted from the byte array.
        }

    }
}
