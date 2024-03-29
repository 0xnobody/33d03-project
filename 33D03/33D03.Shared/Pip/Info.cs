using System; // Importing the System namespace which contains fundamental classes and base classes that define commonly-used value and reference data types, events and event handlers, interfaces, attributes, and processing exceptions.
using System.Collections.Generic; // Importing the namespace for generic collections.
using System.Linq; // Importing the namespace for Language-Integrated Query (LINQ), which provides methods for querying and manipulating data.
using System.Runtime.InteropServices; // Importing the namespace for interaction with COM objects, services, and unmanaged code.
using System.Text; // Importing the namespace for classes representing ASCII and Unicode character encodings.
using System.Threading.Tasks;
using _33D03.Shared.Pip; // Importing the namespace for types that simplify working with tasks, including the ability to execute multiple tasks concurrently.

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

    public struct ClientToServerRequestInfo{
        Header header;

        public  ClientToServerRequestInfo(Header hdr){
            header = hdr;
        }

        public byte[] serialize(){
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
            List<byte> bytesList = new List<byte>();
            // Serialize Header
            bytesList.AddRange(BitConverter.GetBytes(header.magic));
            bytesList.AddRange(BitConverter.GetBytes(header.checksum));
            bytesList.AddRange(BitConverter.GetBytes((uint)header.type));
            bytesList.AddRange(BitConverter.GetBytes((uint)clients.Count));
            // Serialize each ServerListofClients struct
            foreach (var client in clients)
            {
                // Serialize ConvoID
                bytesList.AddRange(BitConverter.GetBytes(client.convoid));
                // Serialize NumberOfFeatures
                bytesList.AddRange(BitConverter.GetBytes(client.numFeatures));
                // Serialize TailData (Features array)
                foreach (var feature in client.features)
                {
                    bytesList.AddRange(BitConverter.GetBytes((short)feature));
                }
            }
            return bytesList.ToArray();
        }

        public static (Header header, List<ServerListofClients> clients) DeserializeListOfServerListofClients(byte[] data)
        {
            int currentIndex = 0;
            Header header = new Header
            {
                magic = BitConverter.ToUInt32(data, currentIndex),
                checksum = BitConverter.ToUInt32(data, currentIndex += sizeof(uint)),
                type = (PacketType)BitConverter.ToUInt32(data, currentIndex += sizeof(uint))
            };
            currentIndex += sizeof(uint);

            uint clientsCount = BitConverter.ToUInt32(data, currentIndex);
            currentIndex += sizeof(uint);

            List<ServerListofClients> clients = new List<ServerListofClients>();

            for (int i = 0; i < clientsCount; i++)
            {
                uint convoid = BitConverter.ToUInt32(data, currentIndex);
                currentIndex += sizeof(uint);

                int numFeatures = BitConverter.ToInt32(data, currentIndex);
                currentIndex += sizeof(int);

                Feature[] features = new Feature[numFeatures];
                for (int j = 0; j < numFeatures; j++)
                {
                    features[j] = (Feature)BitConverter.ToInt16(data, currentIndex);
                    currentIndex += sizeof(short);
                }

                clients.Add(new ServerListofClients
                {
                    convoid = convoid,
                    numFeatures = numFeatures,
                    features = features
                });
            }

            return (header, clients);
        }



    }
}