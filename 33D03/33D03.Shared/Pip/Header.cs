using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    public enum PacketType : ushort // Declaring a public enumeration named PacketType, with underlying type ushort.
    {
        Hello_C2S = 0x0000, // Defining an enumeration member named Hello_C2S with value 0x0000.
        Hello_S2C = 0x0001, // Defining an enumeration member named Hello_S2C with value 0x0001.
        Vote_Request_Simple_C2S = 0x0004,
        Vote_Broadcast_Simple_S2C = 0x0005,
        Vote_answer_Simple_C2S = 0x0006,
        Vote_Broadcast_Vote_Result_Simple_S2C = 0x0007,
        Vote_Request_Vote_C2S = 0x0008, // Defining an enumeration member named Vote_Request_Vote_C2S with value 0x0002.
        Vote_Broadcast_Vote_S2C = 0x0009, // Defining an enumeration member named Vote_Broadcast_Vote_S2C with value 0x0003.
        Vote_Answer_Vote_C2S = 0x00010, // Defining an enumeration member named Vote_Answer_Vote_C2S with value 0x0004.
        Vote_Broadcast_Vote_Result_S2C = 0x00011, // Defining an enumeration member named Vote_Broadcast_Vote_Result_S2C with value 0x0005.
        Client_Info = 0x0006, //s2c client info list
        Client_request_info = 0x0007 //c2s request info list
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct Header // Declaring a public structure named Header.
    {
        public uint magic; // Declaring a field of type uint.
        public uint checksum; // Declaring a field of type uint.
        public PacketType type; // Declaring a field of type PacketType.

        public Header(PacketType pcktType) // Defining a constructor for the struct.
        {
            magic = Constants.MAGIC; // Assigning a constant value to the field magic.
            checksum = 0; // Assigning the value 0 to the field checksum.
            type = pcktType; // Assigning the value of the parameter pcktType to the field type.
        }

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static Header FromBytes(byte[] data) // Defining a static method to create a Header struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<Header>(data); // Returning a Header struct created from the byte array.
        }

        public byte[] Serialize() // Defining a method to serialize the struct into a byte array.
        {
            return ToBytes(); // Returning the byte array representation of the struct.
        }
        public ushort getHeaderType()
        {
            return (ushort)type;
        }
    }
}
