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
    public static class PipServer
    {

        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        internal static void PipServerBroadcastQuestion(TxpServer server, byte[] data, List<ServerVoteId> ServerActiveQuestionList, List<ServerListofClients> clientlist, string filePath)
        {
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            UI.BroadcastingQuestion(question);

            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Vote_S2C);
            Guid voteGuid = recievedpacktestvote.Getguid();

            logger.Info("Client initiate vote requst with SMTLIB question " + question + "Generating Vote with ID " + voteGuid);

            var voteAlreadyExists = ServerActiveQuestionList.Exists(v => v.voteid == voteGuid);

            var numClientsWithSMT = clientlist.Count(c => c.features.Contains(Feature.SMTVerificationFeature));

            if (numClientsWithSMT == 0)
            {
                logger.Warn("Client requested SMTLIB vote, but no clients support SMTLIB. Ignoring.");
                return;
            }

            if (!voteAlreadyExists)
            {
                var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
                var voteinitbytes = Vote_init_packet.Serialize(question);

                foreach (var client in clientlist.Where(c => c.features.Contains(Feature.SMTVerificationFeature)))
                {
                    server.Send(voteinitbytes, server.conversations[client.convoid]);
                }

                ServerVoteId.AddVoteToList(ServerActiveQuestionList, voteGuid, question, 1, numClientsWithSMT);

                new Thread(() =>
                {
                    Thread.Sleep(Shared.Pip.Constants.VOTE_TIMEOUT);

                    var idx = ServerActiveQuestionList.FindIndex(v => v.voteid == voteGuid);
                    if (idx != -1)
                    {
                        logger.Info("Timeout elapsed for vote " + voteGuid + ", broadcasting current response");

                        broadcastVoteResult(server, ServerActiveQuestionList, ServerActiveQuestionList[idx], clientlist, filePath);
                    }
                }).Start();
            }

        }

        internal static void PipServerBroadcastSimpleQuestion(TxpServer server, byte[] data, List<ServerVoteId> ServerActiveQuestionList, List<ServerListofClients> clientlist, string filePath)
        {
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            UI.BroadcastingQuestion(question);
            var sendQuestion = question;
            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Simple_S2C);
            Guid voteGuid = recievedpacktestvote.Getguid();

            logger.Info("Client initiate vote requst with simple question {" + question + "} Generating Vote with ID " + voteGuid);

            var voteAlreadyExists = ServerActiveQuestionList.Exists(v => v.voteid == voteGuid);

            var numClientsWithSimple = clientlist.Count(c => c.features.Contains(Feature.SimpleVerificationFeature));

            if (numClientsWithSimple == 0)
            {
                logger.Warn("Client requested Simple vote, but no clients support Simple Voting. Ignoring.");
                return;
            }

            if (!voteAlreadyExists)
            {
                var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
                var voteinitbytes = Vote_init_packet.Serialize(question);

                foreach (var client in clientlist.Where(c => c.features.Contains(Feature.SimpleVerificationFeature)))
                {
                    logger.Debug($"Sending vote request to client {client.convoid:X}");

                    server.Send(voteinitbytes, server.conversations[client.convoid]);
                }

                int simplecount = clientlist.Count(c => c.features.Contains(Feature.SimpleVerificationFeature));

                ServerVoteId.AddVoteToList(ServerActiveQuestionList, voteGuid, question, 1, simplecount);

                new Thread(() =>
                {
                    Thread.Sleep(Shared.Pip.Constants.VOTE_TIMEOUT);

                    var idx = ServerActiveQuestionList.FindIndex(v => v.voteid == voteGuid);
                    if (idx != -1)
                    {
                        logger.Info("Timeout elapsed for vote " + voteGuid + ", broadcasting current response");

                        broadcastVoteResult(server, ServerActiveQuestionList, ServerActiveQuestionList[idx], clientlist, filePath);
                    }
                }).Start();
            }
        }

        internal static void SendInfo(TxpServer server, TxpClientConversation clientState, List<ServerListofClients> clientsList, byte[] data, uint convoid)
        {
            //Console.WriteLine("sending client list");
            var infohdr = new Header(PacketType.Client_Info);
            var infopack = new PacketInfo(infohdr, clientsList.Count);
            byte[] sendinfobyte = infopack.SerializeListOfServerListofClients(clientsList);

            logger.Debug($"Sending information about {infopack.numClients} clients");

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

            if (!clientsList.Any(c => c.convoid == clientState.ConversationId))
            {
                AddMoreClients(clientsList, convoid, structtest.numFeatures, features);
            }

            var sendhdr = new Header(PacketType.Hello_S2C);
            var hello_back = new PacketHello(sendhdr);
            var serverFeatures = Enum.GetValues<Feature>();
            hello_back.numFeatures = (ushort)serverFeatures.Length;
            var hellos2cdata = hello_back.Serialize(serverFeatures);

            server.Send(hellos2cdata, clientState);

            logger.Debug($"Hello from {clientState.ConversationId} received. Current clients list:");
            foreach (var ServerListofClients in clientsList)
            {
                logger.Debug($"{ServerListofClients.convoid:X} - {ServerListofClients.numFeatures} features - {String.Join(", ", ServerListofClients.features)}");
            }

            //SendInfo(server,clientState ,clientsList,  data,  convoid);
        }

        internal static ushort OrganizeData(TxpServer server, int satcount, int unsatcount, int total)
        {
            if (satcount > unsatcount)
                return 1;
            else if (satcount < unsatcount)
                return 0;
            else
                return 2;
        }

        internal static void handlingvoteresults(TxpServer txpServer, ref List<ServerVoteId> listvote, List<ServerListofClients> clientsList, byte[] data, string filePath)
        {
            PacketAnswerVote voteresultpacket = PacketAnswerVote.FromBytes(data);

            var voteResponse = voteresultpacket.GetResponse();
            var voteGuid = voteresultpacket.GetGuid();

            int j = listvote.FindIndex(c => c.voteid == voteGuid);

            if (j == -1)
            {
                logger.Warn($"Count not find vote for GUID {voteGuid}. Timeout could have elapsed.");
                return;
            }

            ServerVoteId temp = listvote[j];

            if (voteResponse == VoteResponse.SAT)
                temp.sat_counter++;
            else if (voteResponse == VoteResponse.UNSAT)
                temp.unsat_counter++;
            temp.vote_counter += 1;

            listvote[j] = temp;

            logger.Info($"Received vote response {voteResponse} for vote {voteGuid}");
            logger.Info($"Current vote state: {listvote[j].vote_counter} votes, {listvote[j].sat_counter} SAT, {listvote[j].unsat_counter} UNSAT, from {listvote[j].typeclientcount} supporting clients");

            if (listvote[j].vote_counter == listvote[j].typeclientcount)
            {
                broadcastVoteResult(txpServer, listvote, listvote[j], clientsList, filePath);
            }
        }

        private static void broadcastVoteResult(TxpServer txpServer, List<ServerVoteId> listvote, ServerVoteId vote, List<ServerListofClients> clientsList, string filePath)
        {
            var voteGuid = vote.voteid;

            ushort final = PipServer.OrganizeData(txpServer, vote.sat_counter, vote.unsat_counter, vote.vote_counter);
            Guid tempguid = voteGuid;

            int vote_count = vote.vote_counter;
            int sat_counter = vote.sat_counter;
            int unsat_counter = vote.unsat_counter;
            Feature voteFeatureType = vote.votetype == 0 ? Feature.SimpleVerificationFeature : Feature.SMTVerificationFeature;

            listvote.RemoveAll(v => v.voteid == tempguid);

            Header temphdr = new Header(PacketType.Vote_Broadcast_Vote_Result_S2C);
            PacketBroadcastVoteResult ResultS2Cpacket = new PacketBroadcastVoteResult(temphdr, tempguid, final);

            string resultStats = $"Total votes: {vote_count}, Satcount: {sat_counter}, Unsatcount: {unsat_counter}";
            byte[] finaldata = ResultS2Cpacket.Serialize(resultStats);
            UI.BroadcastingResults(resultStats);
            foreach (var client in clientsList.Where(c => c.features.Contains(voteFeatureType)))
            {
                txpServer.Send(finaldata, txpServer.conversations[client.convoid]);
            }

            logger.Info($"Vote {voteGuid}: {resultStats} - Final result is {final}");

            using (StreamWriter writer = new StreamWriter(filePath, true))
            {
                writer.Write(DateTime.Now + " " + voteGuid + " ");
                writer.WriteLine(final);
            }
        }

        internal static void ClientDisconnected(TxpClientConversation clientconversation, List<ServerListofClients> clientsList, TxpServer server)
        {
            logger.Info($"Client disconnected: CID {clientconversation.ConversationId}");

            clientsList.RemoveAll(c => c.convoid == clientconversation.ConversationId);

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
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.WriteLine("                    ||                                                                       ||");
            Console.WriteLine("                    ||                    ,--.                    ,--.  ,--,------,--------. ||");
            Console.WriteLine("                    ||    ,--.  ,--,---.,-'  '-.,---.             |  ,'.|  |  .---'--.  .--' ||");
            Console.WriteLine("                    ||     \\  `'  | .-. '-.  .-| .-. :            |  |' '  |  `--,   |  |    ||");
            Console.WriteLine("                    ||      \\    /' '-' ' |  | \\   --.    .--.    |  | `   |  `---.  |  |    ||");
            Console.WriteLine("                    ||       `--'  `---'  `--'  `----'    '--'    `--'  `--`------'  `--'    ||");
            Console.WriteLine("                    ||                                                                       ||");

            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                                 33D03                               =||");
            Console.WriteLine("                    ||=                                Group 1                              =||");
            Console.WriteLine("                    ||=                    Server Initiated Successfully                    =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.ReadLine();
        }

        internal static void PrintLOGO()
        {
            Console.WriteLine("                    ||                                                                       ||");
            Console.WriteLine("                    ||                    ,--.                    ,--.  ,--,------,--------. ||");
            Console.WriteLine("                    ||    ,--.  ,--,---.,-'  '-.,---.             |  ,'.|  |  .---'--.  .--' ||");
            Console.WriteLine("                    ||     \\  `'  | .-. '-.  .-| .-. :            |  |' '  |  `--,   |  |    ||");
            Console.WriteLine("                    ||      \\    /' '-' ' |  | \\   --.    .--.    |  | `   |  `---.  |  |    ||");
            Console.WriteLine("                    ||       `--'  `---'  `--'  `----'    '--'    `--'  `--`------'  `--'    ||");
            Console.WriteLine("                    ||                                                                       ||");
        }

        public static void ClientConnected(uint convoid)
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                            Client Connected                         =||");
            Console.WriteLine("                    ||=                                   Id                                =||");
            Console.WriteLine($"                    ||=                                    {convoid}                                =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void PrintClientList(List<ServerListofClients> ServerclientsList)
        {
            Console.Clear();
            Thread.Sleep(1);
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            SendInfoUI(ServerclientsList);
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
            Console.WriteLine("||=                                                Feature List                                                 =||");
            foreach (var client in ServerclientsList)
            {
                Console.WriteLine("||---------------------------------------------------------------------------------------------------------------||");
                Console.WriteLine($"||={client.convoid,-10} {client.numFeatures,-5} {client.features[0],-30} {client.features[1],-30} {client.features[2],-30}=||");
                Console.WriteLine("||---------------------------------------------------------------------------------------------------------------||");
            }
            Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
        }


        public static void SendInfoUI(List<ServerListofClients> ServerclientsList)
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                           Sent Info To Client                       =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void BroadcastingQuestion(string question)
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                          Solving For Question                       =||");
            Console.WriteLine("");
            PrintCenteredText(question, 120);
            Console.WriteLine("");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void BroadcastingResults(string results)
        {
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                                 Results                             =||");
            PrintCenteredText(results, 120);
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }




        public static void PrintCenteredText(string text, int lineWidth)
        {
            string[] words = text.Split(' ');
            string line = "";

            foreach (var word in words)
            {
                if ((line + word).Length > lineWidth)
                {
                    Console.WriteLine(CenterLine(line.Trim(), lineWidth));
                    line = word + " ";
                }
                else
                {
                    line += word + " ";
                }
            }
            if (line.Length > 0)
            {
                Console.WriteLine(CenterLine(line.Trim(), lineWidth));
            }
        }

        static string CenterLine(string line, int lineWidth)
        {
            int spacesToAdd = (lineWidth - line.Length) / 2;
            return new string(' ', spacesToAdd) + line;
        }


    }


}