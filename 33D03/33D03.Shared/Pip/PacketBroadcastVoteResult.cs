using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    [StructLayout(LayoutKind.Sequential, Pack = 1)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct PacketBroadcastVoteResult // Declaring a public structure named PacketBroadcastVoteResult.
    {
        Header header; // Declaring a field of type Header.
        Guid voteId; // Declaring a field of type Guid.
        ushort response; // Declaring a field of type ushort.

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static PacketBroadcastVoteResult FromBytes(byte[] data) // Defining a static method to create a PacketBroadcastVoteResult struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<PacketBroadcastVoteResult>(data); // Returning a PacketBroadcastVoteResult struct created from the byte array.
        }

        public byte[] Serialize() // Defining a method to serialize the struct into a byte array.
        {
            return ToBytes(); // Returning the byte array representation of the struct.
        }
    }
}
