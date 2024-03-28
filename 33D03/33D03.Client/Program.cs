using NLog;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using _33D03.Shared.Pip;

namespace _33D03.Client
{
    internal class Program
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        static void WriteLinesFromPreviousLine(string inputFilePath, string outputFilePath)
        {
            // Check if input file exists
            if (File.Exists(inputFilePath))
            {
                // Read lines from input file and write to output file
                using (StreamReader reader = new StreamReader(inputFilePath))
                using (StreamWriter writer = new StreamWriter(outputFilePath))
                {
                    string line;
                    string previousLine = null;

                    while ((line = reader.ReadLine()) != null)
                    {
                        if (previousLine != null)
                        {
                            writer.WriteLine(previousLine);
                        }
                        previousLine = line;
                    }

                    // Write the last line from the input file
                    if (previousLine != null)
                    {
                        writer.WriteLine(previousLine);
                    }
                }
            }
            else
            {
                Console.WriteLine("Input file does not exist.");
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

                TxpClient client = new TxpClient("127.0.0.1", 1151);

                client.OnPacketReceived += (data) =>
                {
                    var pipHeader = Header.FromBytes(data);

                    switch (pipHeader.type)
                    {
                        case PacketType.Vote_Broadcast_Vote_S2C:
                            logger.Trace($"Received packet from Server with data: {PacketBroadcastVote.Deserialize(data)}");
                            (PacketBroadcastVote recievedBroadcastPacket, string question) = PacketBroadcastVote.Deserialize(data);
                            PacketType headerType = recievedBroadcastPacket.HeaderInfo.type;
                            Guid voteID = recievedBroadcastPacket.GetGuid();
                            Console.WriteLine("header type is " + headerType);

                            if (headerType == PacketType.Vote_Broadcast_Vote_S2C)
                            {
                                Console.WriteLine("Solving for smtlib question: " + question);
                                PipClient.ClientAnswerVote(client, question, voteID);
                            }
                            break;

                        case PacketType.Vote_Broadcast_Vote_Result_S2C:
                            logger.Trace($"Received Reuslt packet from server with dat: {PacketBroadcastVoteResult.FromBytes(data)}");
                            PacketBroadcastVoteResult voteResult = PacketBroadcastVoteResult.FromBytes(data);
                            DateTime currentTime = DateTime.Now;
                            string timedata = currentTime + " " + voteResult.GetResponse();
                            string filePath = @"C:\PipList\client_output.txt";
                            using (StreamWriter writer = new StreamWriter(filePath, false))
                            {
                                writer.WriteLine(timedata);
                                Console.WriteLine("wrote to " + filePath);
                            }

                            break;

                    }
                };

                PipClient.VoteInit(client);

                client.Start();

            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the client");
            }

            Thread.Sleep(-1);
        }
    }

}
