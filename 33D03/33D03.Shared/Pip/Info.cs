using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks;
using _33D03.Shared.Pip;
using Microsoft.ML.Data; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

namespace _33D03.Shared.Pip
{
    public struct ServerListofClients
    {
        public uint convoid;
        public int numFeatures;
        public Feature[] features;

        public ServerListofClients(uint id, int num, Feature[] feature)
        {
            convoid = id;
            numFeatures = num;
            features = feature;
        }
    }

    public struct ClientToServerRequestInfo
    {
        Header header;

        public ClientToServerRequestInfo(Header hdr)
        {
            header = hdr;
        }

        public byte[] serialize()
        {
            return Serialization.StructureToByteArray(this);
        }
    }

    public struct PacketInfo
    {
        public Header header;
        public int numClients;

        public PacketInfo(Header hdr, int numclients)
        {
            header = hdr;
            numClients = numclients;
        }

        public byte[] ToBytes() // Defining a method to convert the struct to a byte array.
        {
            return Serialization.StructureToByteArray(this); // Returning the byte array representation of the struct.
        }

        public static Header FromBytes(byte[] data) // Defining a static method to create a Header struct from a byte array.
        {
            return Serialization.ByteArrayToStructure<Header>(data); // Returning a Header struct created from the byte array.
        }

        public byte[] SerializeListOfServerListofClients(List<ServerListofClients> clients)
        {
            // Assuming PacketInfo is the type for 'header' and it is 2 bytes
            int headerSize = 2; // For example, if 'header' consists of a single ushort field
            int numClients = clients.Count;
            int perClientSize = 4 /*convoid*/ + 4 /*numFeatures*/ + 3 * 2 /*features, assuming exactly 2 features per client*/;
            int totalSize = headerSize + 4 /*numClients size*/ + numClients * perClientSize;

            byte[] completedPacketBytes = new byte[totalSize];

            // Assuming ToBytes() correctly serializes the header into 2 bytes
            Buffer.BlockCopy(header.ToBytes(), 0, completedPacketBytes, 0, headerSize);
        
            int currentIndex = headerSize;

            // Serialize number of clients
            Buffer.BlockCopy(Serialization.GetBytes((uint)numClients), 0, completedPacketBytes, currentIndex, 4);
            currentIndex += 4;

            // Serialize each ServerListofClients struct
            foreach (var client in clients)
            {
                Buffer.BlockCopy(Serialization.GetBytes(client.convoid), 0, completedPacketBytes, currentIndex, 4);
                currentIndex += 4;

                Buffer.BlockCopy(Serialization.GetBytes(client.numFeatures), 0, completedPacketBytes, currentIndex, 4);
                currentIndex += 4;

                // Assuming there are at least 3 features per client
                if (client.features.Length >= 3)
                {
                    Buffer.BlockCopy(Serialization.GetBytes((ushort)client.features[0]), 0, completedPacketBytes, currentIndex, 2);
                    currentIndex += 2;

                    Buffer.BlockCopy(Serialization.GetBytes((ushort)client.features[1]), 0, completedPacketBytes, currentIndex, 2);
                    currentIndex += 2;

                    Buffer.BlockCopy(Serialization.GetBytes((ushort)client.features[2]), 0, completedPacketBytes, currentIndex, 2);
                    currentIndex += 2;
                }
            }

            return completedPacketBytes;
        }


        public static (Header header, List<ServerListofClients> clients) DeserializeListOfServerListofClients(byte[] data)
        {
            int currentIndex = 0;
            int headerSize = 2; // The size of the header in bytes

            // Deserialize Header
            Header header = Header.FromBytes(data.Skip(currentIndex).Take(headerSize).ToArray());
            currentIndex += headerSize;

            // Deserialize number of clients
            uint numClients = Serialization.ToUInt32(data, currentIndex);
            currentIndex += 4;

            List<ServerListofClients> clients = new List<ServerListofClients>();

            for (int i = 0; i < numClients; i++)
            {
                // Deserialize ConvoID and NumberOfFeatures
                uint convoid = Serialization.ToUInt32(data, currentIndex);
                currentIndex += 4;

                int numFeatures = Serialization.ToInt32(data, currentIndex);
                currentIndex += 4;

                // Assuming 3 features per client, based on the updated requirement
                Feature[] features = new Feature[3];
                for (int j = 0; j < 3; j++) // Adjusted for 3 features
                {
                    features[j] = (Feature)Serialization.ToUInt16(data, currentIndex);
                    currentIndex += 2;
                }

                clients.Add(new ServerListofClients(convoid, numFeatures, features));
            }

            return (header, clients);
        }


    }
}