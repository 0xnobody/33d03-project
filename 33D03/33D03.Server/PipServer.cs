using NLog;
using System;
using System.Text;
using _33D03.Server;
using System.Timers;
using System.Security.Cryptography.X509Certificates;
using _33D03.Shared.Pip;
using System.ComponentModel;
using System.Runtime.Versioning;
using NLog.LayoutRenderers;
using Microsoft.VisualBasic;
using Google.Protobuf.WellKnownTypes;

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
            var vote = ServerActiveQuestionList.Where(v => v.voteid == voteGuid);
            bool exist = vote.Any();

            if (!exist)
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

                Task.Delay(Shared.Txp.Constants.ACK_TIMEOUT_MS).ContinueWith((Task task) =>
                {
                    if (ServerActiveQuestionList.Any(v => v.voteid == voteGuid))
                    {

                    }
                });
            }
        }

        internal static void SendInfo(TxpServer server, TxpClientConversation clientState, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            var infohdr = new Header(PacketType.Client_Info);
            var infopack = new PacketInfo(infohdr, clientsList.Count);
            byte[] sendinfobyte = infopack.SerializeListOfServerListofClients(clientsList);
            Console.WriteLine($"sent client info{infopack.header} {infopack.numClients}");
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
            if (exists == false)
            {
                AddMoreClients(clientsList, convoid, structtest.numFeatures, features);
            }

            var sendhdr = new Header(PacketType.Hello_S2C);
            byte[] hellos2cdata = sendhdr.ToBytes();
            server.Send(hellos2cdata, clientState);
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine("list");
            foreach (var ServerListofClients in clientsList)
            {
                Console.WriteLine(ServerListofClients.convoid + " " + ServerListofClients.numFeatures + $"{String.Join(", ", ServerListofClients.features)}");
            }
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            //SendInfo(server,clientState ,clientsList,  data,  convoid);
        }

        internal static ushort OrganizeData(TxpServer server, int satcount, int unsatcount, int total)
        {
            if (satcount > unsatcount) return 1;
            else if (satcount <= unsatcount) return 0;
            else return 2;
        }

        internal static void HandleVoteResultReceived(TxpServer txpServer, ref List<ServerVoteId> listvote, List<ServerListofClients> clientsList, byte[] data, string filePath)
        {
            PacketAnswerVote voteresultpacket = PacketAnswerVote.FromBytes(data);

            logger.Info("Client answered vote");
            Console.WriteLine("vote counter + 1");
            
            int j = 0;
            foreach (var ServerVoteID in listvote)
            {
                
                if (ServerVoteID.voteid == voteresultpacket.GetGuid())
                {
                    break;
                }
                j++;
            }

            ServerVoteId temp = listvote[j];
            if (voteresultpacket.GetResponse() == 1) temp.sat_counter++;
            else if (voteresultpacket.GetResponse() == 0) temp.unsat_counter++;

            temp.vote_counter += 1;
            listvote[j] = temp;

            Console.WriteLine(listvote[j].vote_counter + " " + listvote[j].unsat_counter + " " + listvote[j].sat_counter);
            Console.WriteLine(voteresultpacket.GetResponse());
            Console.WriteLine(txpServer.conversations.Count);

            Console.WriteLine();

            if (listvote[j].vote_counter == clientsList.Count)
            {
                BroadcastVoteResult(txpServer, listvote[j], listvote, clientsList, filePath);
            }
        }

        private static void BroadcastVoteResult(TxpServer txpServer, ServerVoteId vote, List<ServerVoteId> listvote, List<ServerListofClients> clientsList, string filePath)
        {
            var final = PipServer.OrganizeData(txpServer, vote.unsat_counter, vote.sat_counter, vote.vote_counter);
            Guid tempguid = vote.voteid;

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

            int vote_count = vote.vote_counter;
            int sat_counter = vote.sat_counter;
            int unsat_counter = vote.unsat_counter;
            string resultStats = $"Total votes: {vote_count}, Satcount: {sat_counter}, Unsatcount: {unsat_counter}";

            byte[] finaldata = ResultS2Cpacket.Serialize(resultStats);
            foreach (var client in clientsList)
            {
                var conversations = txpServer.conversations.Where(c => c.Key == client.convoid);

                if (!conversations.Any())
                {
                    logger.Warn($"Conversation not found for CID {client.convoid}")
                }
                txpServer.Send(finaldata, conversations.FirstOrDefault().Value);
            }

            Console.WriteLine(vote_count + " " + unsat_counter + " " + sat_counter);
            logger.Info($"final packet result for guid {vote.voteid} is {final}");

            var ServerLogToWrite = new ServerVoteLog(vote.voteid, final);
            DateTime currentTime = DateTime.Now;

            using (StreamWriter writer = new StreamWriter(filePath, true))
            {
                writer.Write(currentTime + " " + ServerLogToWrite.GetGuid() + " ");
                writer.WriteLine(final);
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