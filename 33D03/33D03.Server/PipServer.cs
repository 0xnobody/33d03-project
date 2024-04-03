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

        internal static void PipServerBroadcastQuestion(TxpServer server, byte[] data, List<ServerVoteId> ServerActiveQuestionList, List<ServerListofClients> clientlist)
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
            int smtcount = 0;
            foreach (var ServerListofClients in clientlist)
            {
                for (int i = 0; i < ServerListofClients.numFeatures; i++)
                {
                    if (ServerListofClients.features[i] == Feature.SMTVerificationFeature && ServerListofClients.convoid != 0)
                    {
                        smtcount++;
                        break;
                    }
                }
            }
            if (exist == false && smtcount != 0)
            {
                var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
                var voteinitbytes = Vote_init_packet.Serialize(question);
                foreach (var conversationEntry in server.conversations)
                {
                    var conversation = conversationEntry.Value;
                    server.Send(voteinitbytes, conversation);
                    logger.Info("Client initiate vote requst with SMTLIB question " + question + "Generating Vote with ID " + voteGuid);
                }



                ServerVoteId.AddVoteToList(ServerActiveQuestionList, voteGuid, question, 1, smtcount);
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
            else if (smtcount == 0)
            {
                Console.WriteLine("Cannot have 0 clients");
            }

        }

        internal static void PipServerBroadcastSimpleQuestion(TxpServer server, byte[] data, List<ServerVoteId> ServerActiveQuestionList, List<ServerListofClients> clientlist)
        {
            foreach (ServerVoteId ServerVoteId in ServerActiveQuestionList)
            {
                Console.WriteLine($"ServerVoteID{ServerVoteId.voteid}, Question{ServerVoteId.question}");
            }
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            var sendQuestion = question;
            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Simple_S2C);
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
                    logger.Info("Client initiate vote requst with simple question " + question + "Generating Vote with ID " + voteGuid);
                }

                int simplecount = 0;
                foreach (var ServerListofClients in clientlist)
                {
                    for (int i = 0; i < ServerListofClients.numFeatures; i++)
                    {
                        if (ServerListofClients.features[i] == Feature.SimpleVerificationFeature && ServerListofClients.convoid != 0)
                        {
                            {
                                Console.WriteLine("added simple count");
                                simplecount++;
                                break;
                            }

                        }
                    }
                }

                ServerVoteId.AddVoteToList(ServerActiveQuestionList, voteGuid, question, 1, simplecount);
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine();
                foreach (ServerVoteId ServerVoteId in ServerActiveQuestionList)
                {
                    Console.WriteLine($"ServerVoteID{ServerVoteId.voteid}, Question{ServerVoteId.question}, Question type {ServerVoteId.votetype} with clientcount {ServerVoteId.typeclientcount}");
                }
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine();
            }

        }

        internal static void SendInfo(TxpServer server, TxpClientConversation clientState, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            Console.WriteLine("sending client list");
            var infohdr = new Header(PacketType.Client_Info);
            var infopack = new PacketInfo(infohdr, clientsList.Count);
            byte[] sendinfobyte = infopack.SerializeListOfServerListofClients(clientsList);
            Console.WriteLine($"sent client info{infopack.header} {infopack.numClients}");
            Console.WriteLine(BitConverter.ToString(sendinfobyte));
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

        internal static void handlingvoteresults(TxpServer txpServer, ref List<ServerVoteId> listvote, byte[] data, string filePath)
        {
            PacketAnswerVote voteresultpacket = PacketAnswerVote.FromBytes(data);
            logger.Info("Client answered vote");
            Console.WriteLine("vote counter + 1");
            ushort final = 0;
            int j = 0;
            foreach (var ServerVoteID in listvote)
            {

                if (ServerVoteID.voteid == voteresultpacket.GetGuid())
                {
                    break;
                }
                j++;
            }
            Console.WriteLine(listvote[j].vote_counter + " " + listvote[j].unsat_counter + " " + listvote[j].sat_counter + "      " + listvote[j].typeclientcount);
            ServerVoteId temp = listvote[j];
            Console.WriteLine("temp alloc successful");
            if (voteresultpacket.GetResponse() == 1) temp.sat_counter++;
            else if (voteresultpacket.GetResponse() == 0) temp.unsat_counter++;
            temp.vote_counter += 1;
            listvote[j] = temp;
            Console.WriteLine(listvote[j].vote_counter + " " + listvote[j].unsat_counter + " " + listvote[j].sat_counter + "      " + listvote[j].typeclientcount);
            Console.WriteLine(voteresultpacket.GetResponse());
            Console.WriteLine(txpServer.conversations.Count);
            Console.WriteLine();
            if (listvote[j].vote_counter == listvote[j].typeclientcount)
            {
                final = PipServer.OrganizeData(txpServer, listvote[j].unsat_counter, listvote[j].sat_counter, listvote[j].vote_counter);
                Guid tempguid = voteresultpacket.GetGuid();


                int listcount = listvote.Count;
                int vote_count = listvote[j].vote_counter;
                int sat_counter = listvote[j].sat_counter;
                int unsat_counter = listvote[j].unsat_counter;
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
                string resultStats = $"Total votes: {vote_count}, Satcount: {sat_counter}, Unsatcount: {unsat_counter}";
                byte[] finaldata = ResultS2Cpacket.Serialize(resultStats);
                foreach (var conversationEntry in txpServer.conversations)
                {
                    var conversation = conversationEntry.Value;
                    txpServer.Send(finaldata, conversation);
                }
                Console.WriteLine(vote_count + " " + unsat_counter + " " + sat_counter);
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


    public class UI
    {

        public static void StartupUIServer()
        {
            Console.Clear();
            Console.WriteLine("---------------------------------------------------------------------------");
            Console.WriteLine("||                                                                       ||");
            Console.WriteLine("||                    ,--.                    ,--.  ,--,------,--------. ||");
            Console.WriteLine("||    ,--.  ,--,---.,-'  '-.,---.             |  ,'.|  |  .---'--.  .--' ||");
            Console.WriteLine("||     \\  `'  | .-. '-.  .-| .-. :            |  |' '  |  `--,   |  |    ||");
            Console.WriteLine("||      \\    /' '-' ' |  | \\   --.    .--.    |  | `   |  `---.  |  |    ||");
            Console.WriteLine("||       `--'  `---'  `--'  `----'    '--'    `--'  `--`------'  `--'    ||");
            Console.WriteLine("||                                                                       ||");

            Console.WriteLine("||=======================================================================||");
            Console.WriteLine("||=                                 33D03                               =||");
            Console.WriteLine("||=                                Group 1                              =||");
            Console.WriteLine("||=                    Server Initiated Successfully                    =||");
            Console.WriteLine("||=======================================================================||");
            Console.WriteLine("---------------------------------------------------------------------------");
            Console.ReadLine();
        }

        public static void PrintClientList()
        {

        }


    }


}