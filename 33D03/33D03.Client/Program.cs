using NLog;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using _33D03.Shared;
using _33D03.Shared.Pip;
using Microsoft.VisualBasic;

namespace _33D03.Client
{
    internal class Program
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();


        public static void ProcessInput(object objclient){
            TxpClient client = objclient as TxpClient;
            string input = null;
            while(input != "exit"){
                input = Console.ReadLine();
                if (input == "vote"){
                    PipClient.VoteInit(client);
                }
                else if (input == "info"){
                    PipClient.Client_request_info(client);
                }
                else if (input == "help"){
                    helpPrint();
                }
                else if (input == "flood"){

                    byte [] Getbytes = PipClient.GethelloBytes();
                    byte [] Getinfobytes = PipClient.GetinfoBytes();
                    while (1 == 1){
                        client.Send(Getbytes);
                        client.Send(Getinfobytes);
                    }
                }
            }
        }


        private static void Main(string[] args)
        {
            try
            {
                // Setup logging
                NLog.LogManager.Setup().LoadConfiguration(builder =>
                {
                    builder.ForLogger().FilterMinLevel(LogLevel.Trace).WriteToColoredConsole();
                });

                TxpClient client = new TxpClient("192.168.50.19", 24588);
                string filePath = @$"C:\PipList\client{Guid.NewGuid()}_output.txt";
                client.OnPacketReceived += (data) =>
                {
                    //OnPacketRecievedHandler(client, data);
                };

                Thread StartThread = new Thread (new ThreadStart(client.Start));
                StartThread.Start();

                Thread inputThread = new Thread (new ParameterizedThreadStart(ProcessInput));
                inputThread.Start(client);

                

                PipClient.SendHello(client);

                helpPrint();       



            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the client");
            }

            Thread.Sleep(-1);
        }



        private static void helpPrint(){
                Console.WriteLine("Inputs:");
                Console.WriteLine("vote -- initiate vote");
                Console.WriteLine("info -- request Client list from server");
                Console.WriteLine("exit -- exits");       
        }


        private static void OnVoteBroadCastVoteS2C(TxpClient client, String filePath, byte[] data)
        {
            logger.Trace($"Received packet from Server with data: {PacketBroadcastVote.Deserialize(data)}");
            (PacketBroadcastVote recievedBroadcastPacket, string question) = PacketBroadcastVote.Deserialize(data);
            PacketType headerType = recievedBroadcastPacket.HeaderInfo.type;
            Guid voteID = recievedBroadcastPacket.GetGuid();
            Console.WriteLine("header type is " + headerType);

            if (headerType == PacketType.Vote_Broadcast_Vote_S2C)
            {
                Console.WriteLine("Solving for smtlib question: " + question);
                PipClient.ClientAnswerVote(client, question, voteID);
                DateTime currentTimes = DateTime.Now;
                string timedatas = currentTimes + " ";
                using (StreamWriter writer = new StreamWriter(filePath, true))
                {
                    writer.Write(timedatas + " " + question + " ");
                    Console.WriteLine("wrote to " + filePath);
                }
            }
        }

        private static void OnVoteBroadCastVoteS2C(string filePath, byte[] data)
        {
            logger.Trace($"Received Reuslt packet from server with dat: {PacketBroadcastVoteResult.FromBytes(data)}");
            PacketBroadcastVoteResult voteResult = PacketBroadcastVoteResult.FromBytes(data);
            DateTime currentTime = DateTime.Now;


            using (StreamWriter writer = new StreamWriter(filePath, true))
            {
                writer.WriteLine(voteResult.GetResponse() + " " + voteResult.GetGuid());
                Console.WriteLine("wrote to " + filePath);
            }
        }


        private static void OnPacketRecievedHandler(TxpClient client, byte[] data)
        {
            var pipHeader = Header.FromBytes(data);
            string filePath = @$"C:\PipList\client{Guid.NewGuid()}_output.txt";

            switch (pipHeader.type)
            {
                case PacketType.Vote_Broadcast_Vote_S2C:
                    OnVoteBroadCastVoteS2C(client, filePath, data);
                    break;

                case PacketType.Vote_Broadcast_Vote_Result_S2C:
                    OnVoteBroadCastVoteS2C(filePath, data);
                    break;

                case PacketType.Hello_S2C:
                    Console.WriteLine("server waved hello!");
                    break;
                case PacketType.Client_Info:
                    (Header hdr, List<ServerListofClients> infolist) = PacketInfo.DeserializeListOfServerListofClients(data);
                    foreach (var ServerListofClients in infolist)
                    {
                        Console.WriteLine($"Recieved, ClientID: {ServerListofClients.convoid}, numfeatures {ServerListofClients.numFeatures}, Features:{String.Join(", ", ServerListofClients.features)}");
                    }
                    break;

            }
        }
    }
}