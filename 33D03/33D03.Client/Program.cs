﻿using NLog;
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


        public static void ProcessInput(object objclient)
        {
            TxpClient client = objclient as TxpClient;
            string input = null;
            while (input != "exit")
            {
                input = Console.ReadLine();
                if (input == "vote")
                {
                    PipClient.VoteInit(client);
                }
                else if (input == "info")
                {
                    PipClient.Client_request_info(client);
                }
                else if (input == "help")
                {
                    helpPrint();
                }
                else if (input == "votesimple")
                {
                    PipClient.VoteSimpleInit(client);
                }
                else if (input == "flood")
                {

                    byte[] Getbytes = PipClient.GethelloBytes();
                    byte[] Getinfobytes = PipClient.GetinfoBytes();
                    while (1 == 1)
                    {
                        client.Send(Getbytes);
                        client.Send(Getinfobytes);
                    }
                }
            }
        }

        public static Feature[] SelectInput()
        {
            string input = "something string";
            Console.WriteLine("Feature selection");
            Console.WriteLine("1 for smt eval feature");
            Console.WriteLine("2 for ocr eval feature");
            Feature[] features = new Feature[3];
            int count = 0;
            while (input != "" && input != null)
            {
                input = Console.ReadLine();
                if (count == 3) break;
                if (input == "1")
                {
                    bool hassmt = false;
                    for (int i = 0; i < count; i++)
                    {

                        if (features[i] == Feature.SMTVerificationFeature)
                        {
                            hassmt = true;
                            break;
                        }
                    }
                    if (hassmt == false)
                    {
                        features[count] = Feature.SMTVerificationFeature;
                        count++;
                    };
                }
                else if (input == "0")
                {
                    bool hassmt = false;
                    for (int i = 0; i < count; i++)
                    {

                        if (features[i] == Feature.SimpleVerificationFeature)
                        {
                            hassmt = true;
                            break;
                        }
                    }
                    if (hassmt == false)
                    {
                        features[count] = Feature.SimpleVerificationFeature;
                        count++;
                    };
                }

                else if (input == "2")
                {
                    bool hasocr = false;
                    for (int i = 0; i < count; i++)
                    {

                        if (features[i] == Feature.OCRFeature)
                        {
                            hasocr = true;
                            break;
                        }
                    }
                    if (hasocr == false)
                    {
                        features[count] = Feature.OCRFeature;
                        count++;
                    };
                }
            }

            return features;
        }


        private static void Main(string[] args)
        {
            try
            {
                // Setup logging
                NLog.LogManager.Setup().LoadConfiguration(builder =>
                {
                    builder.ForLogger().FilterMinLevel(LogLevel.Debug).WriteToColoredConsole();
                });

                string test = PipClient.GenerateEvalString();
                Console.WriteLine(test);

                Feature[] features = SelectInput();
                bool HasSmtVerification = false;
                for (int i = 0; i < 3; i++)
                {

                    if (features[i] == Feature.SMTVerificationFeature)
                    {
                        HasSmtVerification = true;
                        break;
                    }
                }

                TxpClient client = new TxpClient("33d03-project.college", 24588);
                string filePath = @$"C:\PipList\client{Guid.NewGuid()}_output.txt";
                client.OnPacketReceived += (data) =>
                {
                    logger.Trace($"client received data {BitConverter.ToString(data).Replace("-", "")}");

                    OnPacketRecievedHandler(client, data, HasSmtVerification);
                };
                
                client.Start();

                Thread inputThread = new Thread(new ParameterizedThreadStart(ProcessInput));
                inputThread.Start(client);

                PipClient.SendHello(client, features);

                helpPrint();



            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the client");
            }

            Thread.Sleep(-1);
        }



        private static void helpPrint()
        {
            Console.WriteLine("Inputs:");
            Console.WriteLine("vote -- initiate vote");
            Console.WriteLine("info -- request Client list from server");
            Console.WriteLine("exit -- exits");
            Console.WriteLine("votesimple -- eval non smt equations");
            Console.WriteLine("flood -- floods server, but client uses more resources, even when ignoring incopming packets...");
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

        private static void OnVoteBroadCastVoteResultS2C(string filePath, byte[] data)
        {
            logger.Trace($"Received Reuslt packet from server with dat: {PacketBroadcastVoteResult.FromBytes(data)}");
            (PacketBroadcastVoteResult voteResult, string resultStats) = PacketBroadcastVoteResult.Deserialize(data);
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine(resultStats);
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            DateTime currentTime = DateTime.Now;


            using (StreamWriter writer = new StreamWriter(filePath, true))
            {
                writer.WriteLine(voteResult.GetResponse() + " " + voteResult.GetGuid());
                Console.WriteLine("wrote to " + filePath);
            }
        }

        private static void OnVoteBroadCastSimpleVoteS2C(TxpClient client, string filePath, byte[] data)
        {
            logger.Trace($"Received packet from Server with data: {PacketBroadcastVote.Deserialize(data)}");
            (PacketBroadcastVote recievedBroadcastPacket, string question) = PacketBroadcastVote.Deserialize(data);
            PacketType headerType = recievedBroadcastPacket.HeaderInfo.type;
            Guid voteID = recievedBroadcastPacket.GetGuid();
            Console.WriteLine("header type is " + headerType);
            if (headerType == PacketType.Vote_Broadcast_Simple_S2C)
            {
                Console.WriteLine("Solving for smtlib question: " + question);
                PipClient.ClientAnswerVoteSimple(client, question, voteID);
                DateTime currentTimes = DateTime.Now;
                string timedatas = currentTimes + " ";
                using (StreamWriter writer = new StreamWriter(filePath, true))
                {
                    writer.Write(timedatas + " " + question + " ");
                    Console.WriteLine("wrote to " + filePath);
                }
            }
        }


        private static void OnPacketRecievedHandler(TxpClient client, byte[] data, bool ClientSmtCapabilities)
        {
            var pipHeader = Header.FromBytes(data);
            string filePath = @$"C:\PipList\client{Guid.NewGuid()}_output.txt";

            switch (pipHeader.type)
            {
                case PacketType.Vote_Broadcast_Vote_S2C:
                    if (ClientSmtCapabilities == true)
                    {
                        OnVoteBroadCastVoteS2C(client, filePath, data);
                    }
                    else Console.WriteLine("cannot solve for smt question type");
                    break;

                case PacketType.Vote_Broadcast_Vote_Result_S2C:
                    OnVoteBroadCastVoteResultS2C(filePath, data);
                    break;
                case PacketType.Vote_Broadcast_Simple_S2C:
                    OnVoteBroadCastSimpleVoteS2C(client, filePath, data);
                    break;
                case PacketType.Hello_S2C:
                    Console.WriteLine("server waved hello!");
                    break;
                case PacketType.Client_Info:
                    (Header hdr, List<ServerListofClients> infolist) = PacketInfo.DeserializeListOfServerListofClients(data);
                    foreach (var ServerListofClients in infolist)
                    {
                        if (ServerListofClients.convoid != 0)
                        {
                            Console.WriteLine($"Recieved, ClientID: {ServerListofClients.convoid}, numfeatures {ServerListofClients.numFeatures}, Features:{String.Join(", ", ServerListofClients.features)}");
                        }
                        else { Console.WriteLine($"Recieved, SERVER BROADCASST, Server has numfeatures: {ServerListofClients.numFeatures}, Features:{String.Join(", ", ServerListofClients.features)}"); }
                    }
                    break;

            }
        }
    }
}