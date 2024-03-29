using NLog;
using System;
using System.Text;
using _33D03.Server;
using System.Security.Cryptography.X509Certificates;
using _33D03.Shared.Pip;
using System.ComponentModel;
using System.Runtime.Versioning;
using NLog.LayoutRenderers;

namespace _33D03.Server
{

    public struct ServerVoteLog
    {
        Guid servervoteguid;
        ushort result;

        public ServerVoteLog(Guid inputGuid, ushort rest)
        {
            servervoteguid = inputGuid;
            result = rest;
        }
        public Guid GetGuid()
        {
            return servervoteguid;
        }
        public ushort GetResult()
        {
            return result;
        }
    }

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


    public static class PipServer
    {

        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();
        internal static void PipServerBroadcastQuestion(TxpServer server, byte[] data)
        {
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            var sendQuestion = question;
            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Vote_S2C);
            Guid voteGuid = Guid.NewGuid();
            var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
            var voteinitbytes = Vote_init_packet.Serialize(question);
            foreach (var conversationEntry in server.conversations)
            {
                var conversation = conversationEntry.Value;
                server.Send(voteinitbytes, conversation);
                logger.Info("Client initiate vote requst with SMTLIB question" + question + "Generating Vote with ID " + voteGuid);
            }
        }

        struct questionID
        {

        }

        static void AddMoreClients(List<ServerListofClients> clientsList, uint convoid, int numFeatures, Feature[] features)
        {
            clientsList.Add(new ServerListofClients(convoid, numFeatures, features));
        }

        internal static void HelloRecieved(TxpServer server, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            Header header = PacketHello.FromBytes(data);
            (PacketHello structtest, Feature[] features) = PacketHello.Deserialize(data);
            AddMoreClients(clientsList, convoid, structtest.numFeatures, features);
            Console.WriteLine($"ID: {convoid}, NumFeatures: {structtest.numFeatures}, features: {String.Join(", ", features)}");
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine("List of Packets:");
            foreach (var ServerListofClients in clientsList)
            {
                Console.WriteLine($"ID: {ServerListofClients.convoid}, NumFeatures: {ServerListofClients.numFeatures}, features: {String.Join(", ", ServerListofClients.features)}");
            }
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
        }

        internal static ushort OrganizeData(TxpServer server, int satcount, int unsatcount, int total)
        {
            if (satcount > unsatcount) return 1;
            else if (satcount <= unsatcount) return 0;
            else return 2;
        }

        internal static void ServerCalculatesVotes()
        {



        }
        internal static void ClientDisconnected(TxpClientConversation clientconversation, List<ServerListofClients> clientsList, TxpServer server)
        {
            logger.Info($"Client disconnected: CID {clientConversation.convoid}");

            for(int i = 0; i < clientsList.Count; i++)//iterates through clientlist
            {
                if (clientsList[i].convoid == clientconversation.convoid)
                {
                    clientsList.RemoveAt(i);
                    break; //Exits loop once the client is found and removed from list
                }
            }
            BroadcastUpdatedClientList(clientsList, server);
        }

        internal static void BroadcastUpdatedClientList(List<ServerListofClients> clientsList, TxpServer server)
        {
            byte[] clientListBytes = Serialize(clientsList);
            server.Broadcast(clientsListBytes);
        }
    }
}
