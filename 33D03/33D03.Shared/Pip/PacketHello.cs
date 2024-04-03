using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Net;
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.


namespace _33D03.Shared.Pip // Declaring a namespace for organizing related code and reducing naming conflicts.
{
    public enum Feature : ushort // Declaring a public enumeration named Feature, with underlying type ushort.
    {
        NULL = 0,
        SimpleVerificationFeature = 1,
        SMTVerificationFeature = 2, // Defining an enumeration member named SMTVerificationFeature with value 0.
        OCRFeature = 3,
        PacketSegmentationFeature = 4,
    }

    [StructLayout(LayoutKind.Sequential, Pack = 1, Size = 8)] // Applying an attribute to control the physical layout of the data fields in this struct when it is passed to unmanaged code.
    public struct PacketHello // Declaring a public structure named PacketHello.
    {
        public Header header; // Declaring a field of type Header.
        public uint version; // Declaring a field of type uint.
        public ushort numFeatures;

        public PacketHello(Header hdr)
        {
            header = hdr;
            version = Constants.VERSION;
            numFeatures = 0;
        }

        public Header HeaderInfo
        {
            get { return header; }
        }

        public uint GetVersion()
        {
            return version;
        }

        //public Feature[] GetFeaturesArray(){
        //return feature;
        //}

        public int GetNumFeatures()
        {
            return numFeatures;
        }

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static Header FromBytes(byte[] data) // Defining a static method to create a Header struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<Header>(data); // Returning a Header struct created from the byte array.
        }

        public byte[] Serialize(Feature[] features) // Defining a method to serialize the struct along with a features array into a byte array.
        {
            if (features.Length != numFeatures) // Checking if the length of the features array matches the expected length.
            {
                throw new ArgumentException("Incorrect number of features"); // Throwing an exception if the lengths do not match.
            }

            var completedPacketBytes = new byte[Marshal.SizeOf(this) + numFeatures * 2]; // Creating a byte array to hold the serialized struct and features array.
            Buffer.BlockCopy(ToBytes(), 0, completedPacketBytes, 0, Marshal.SizeOf(typeof(PacketHello))); // Assuming ToBytes() serializes the PacketHello struct
            int startIndexOfFeatures = Marshal.SizeOf(typeof(PacketHello)); // Adjust if header needs specific handling
            for (int i = 0; i < numFeatures; i++)
            {
                Buffer.BlockCopy(Serialization.GetBytes((ushort)features[i]), 0, completedPacketBytes, startIndexOfFeatures + i * 2, 2);
            }

            return completedPacketBytes; // Returning the completed byte array.
        }

        public static (PacketHello, Feature[]) Deserialize(byte[] data)
        {
            // Extract the PacketHello structure
            var packetHello = Serialization.ByteArrayToStructure<PacketHello>(data);

            // Assuming you know how many features there are (e.g., from packetHello or a fixed size)
            // For demonstration, let's say it's a fixed number or extracted from packetHello
            int numFeatures = packetHello.numFeatures;
            Feature[] features = new Feature[numFeatures];

            int featuresStartIndex = Marshal.SizeOf<PacketHello>();
            for (int i = 0; i < numFeatures; i++)
            {
                int featurePos = featuresStartIndex + (i * sizeof(ushort));
                features[i] = (Feature)Serialization.ToUInt16(data, featurePos);
            }
            return (packetHello, features);
        }


        public static Feature[] GetFeatures(byte[] fullPacketData, int numFeatures, Header header) // Defining a method to extract the features array from a serialized PacketHello.
        {
            Feature[] features = new Feature[numFeatures]; // Creating a new features array.
            for (int i = 0; i < numFeatures; i++) // Looping over each feature.
            {
                features[i] = (Feature)Serialization.ToUInt16(fullPacketData, Marshal.SizeOf(header) + i * 2); // Converting each feature from a byte array to a Feature enumeration member and storing it in the features array.
            }
            return features; // Returning the features array.
        }
    }
}
