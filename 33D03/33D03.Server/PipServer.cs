using NLog;
using System;
using System.Text;
using _33D03.Server;
using System.Security.Cryptography.X509Certificates;
using _33D03.Shared.Pip;
using System.ComponentModel;
using System.Runtime.Versioning;
using NLog.LayoutRenderers;
using Microsoft.VisualBasic;

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


    public static class PipServer
    {

        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        internal static void PipServerBroadcastQuestion(TxpServer server, byte[] data, List<ServerVoteId> ServerActiveQuestionList)
        {
            foreach (ServerVoteId ServerVoteId in ServerActiveQuestionList)
            {
                Console.WriteLine($"ServerVoteID{ServerVoteId.voteid}, Question{ServerVoteId.question}");
            }
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            var sendQuestion = question;
            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Vote_S2C);
            Guid voteGuid = recievedpacktestvote.Getguid();
            bool exist = false;
            foreach (ServerVoteId ServerVoteId in ServerActiveQuestionList)
            {
                Console.WriteLine("FALSE REPORTED");
                if (ServerVoteId.voteid == voteGuid)
                {
                    exist = true;
                }
            }
            if (exist == false)
            {
                var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
                var voteinitbytes = Vote_init_packet.Serialize(question);
                foreach (var conversationEntry in server.conversations)
                {
                    var conversation = conversationEntry.Value;
                    server.Send(voteinitbytes, conversation);
                    logger.Info("Client initiate vote requst with SMTLIB question" + question + "Generating Vote with ID " + voteGuid);

                }
                ServerVoteId.AddVoteToList(ServerActiveQuestionList, voteGuid, question);
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine();
                foreach (ServerVoteId ServerVoteId in ServerActiveQuestionList)
                {
                    Console.WriteLine($"ServerVoteID{ServerVoteId.voteid}, Question{ServerVoteId.question}");
                }
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine();
            }

        }



        internal static void SendInfo(TxpServer server, TxpClientConversation clientState, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            var infohdr = new Header(PacketType.Client_Info);
            var infopack = new PacketInfo(infohdr, clientsList.Count);
            byte[] sendinfobyte = infopack.SerializeListOfServerListofClients(clientsList);
            server.Send(sendinfobyte, clientState);
        }

        internal static void AddMoreClients(List<ServerListofClients> clientsList, uint convoid, int numFeatures, Feature[] features)
        {
            clientsList.Add(new ServerListofClients(convoid, numFeatures, features));
        }

        internal static void HelloRecieved(TxpServer server, TxpClientConversation clientState, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            Header header = PacketHello.FromBytes(data);
            (PacketHello structtest, Feature[] features) = PacketHello.Deserialize(data);
            bool exists = false;
            foreach (var ServerListofClients in clientsList)
            {
                if (ServerListofClients.convoid == clientState.ConversationId)
                {
                    exists = true;
                    break;
                }
            }
            if (exists == true)
            {
                AddMoreClients(clientsList, convoid, structtest.numFeatures, features);
            }

            var sendhdr = new Header(PacketType.Hello_S2C);
            byte[] hellos2cdata = sendhdr.ToBytes();
            server.Send(hellos2cdata, clientState);
            //SendInfo(server,clientState ,clientsList,  data,  convoid);
        }

        internal static ushort OrganizeData(TxpServer server, int satcount, int unsatcount, int total)
        {
            if (satcount > unsatcount) return 1;
            else if (satcount <= unsatcount) return 0;
            else return 2;
        }

        internal static void handlingvoteresults(TxpServer txpServer, List<ServerVoteId> listvote, byte[] data, int vote_counter, int satcount, int unsatcount, string filePath)
        {
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine(txpServer.conversations.Count);
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            PacketAnswerVote voteresultpacket = PacketAnswerVote.FromBytes(data);
            logger.Info("Client answered vote");
            vote_counter += 1;
            ushort final = 0;
            if (voteresultpacket.GetResponse() == 1) satcount++;
            else if (voteresultpacket.GetResponse() == 0) unsatcount++;
            Console.WriteLine(vote_counter + " " + unsatcount + " " + satcount);
            Console.WriteLine(voteresultpacket.GetResponse());
            Console.WriteLine();
            Console.WriteLine();
            if (vote_counter == txpServer.conversations.Count)
            {
                final = PipServer.OrganizeData(txpServer, unsatcount, satcount, vote_counter);
                Guid tempguid = voteresultpacket.GetGuid();


                int listcount = listvote.Count;

                for (int i = listvote.Count - 1; i >= 0; i--)
                {
                    if (listvote[i].voteid == tempguid)
                    {
                        listvote.RemoveAt(i); 
                        break; 
                    }
                }




                Header temphdr = new Header(PacketType.Vote_Broadcast_Vote_Result_S2C);
                PacketBroadcastVoteResult ResultS2Cpacket = new PacketBroadcastVoteResult(temphdr, tempguid, final);
                byte[] finaldata = ResultS2Cpacket.ToBytes();
                foreach (var conversationEntry in txpServer.conversations)
                {
                    var conversation = conversationEntry.Value;
                    txpServer.Send(finaldata, conversation);
                }
                vote_counter = 0;
                unsatcount = 0;
                satcount = 0;
                Console.WriteLine(vote_counter + " " + unsatcount + " " + satcount);
                logger.Info($"final packet result for guid {voteresultpacket.GetGuid()} is {final}");
                var ServerLogToWrite = new ServerVoteLog(voteresultpacket.GetGuid(), final);
                DateTime currentTime = DateTime.Now;

                using (StreamWriter writer = new StreamWriter(filePath, true))
                {
                    writer.Write(currentTime + " " + ServerLogToWrite.GetGuid() + " ");
                    writer.WriteLine(final);
                }
            }
        }

        internal static void ClientDisconnected(TxpClientConversation clientconversation, List<ServerListofClients> clientsList, TxpServer server)
        {
            logger.Info($"Client disconnected: CID {clientconversation.ConversationId}");

            for (int i = clientsList.Count - 1; i >= 0; i--)
            {
                if (clientsList[i].convoid == clientconversation.ConversationId)
                {
                    clientsList.RemoveAt(i);
                    // If you're sure there's only one client to remove, you can break after removing.
                    break;
                }
            }
            BroadcastUpdatedClientList(clientsList, server);
        }

        internal static void BroadcastUpdatedClientList(List<ServerListofClients> clientsList, TxpServer server)
        {
            Header hdr = new Header(PacketType.Client_Info);
            var InfoToSend = new PacketInfo(hdr, clientsList.Count);
            byte[] clientListBytes = InfoToSend.SerializeListOfServerListofClients(clientsList);
            server.Broadcast(clientListBytes);
        }

    }
}