
using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Serialization;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared;
using _33D03.Shared.Pip;
using System.Data.SqlTypes;

namespace _33D03.Server
{
    internal class Program
    {
        // Creates a logger instance for this class using NLog.
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        // Dictionary to store clients and their features
        private static Dictionary<Guid, Feature[]> clientFeatures = new Dictionay<Guid, Feature[]>();

        private static void Main(string[] args)
        {
            try
            {
                // Setup NLog logging configuration.
                NLog.LogManager.Setup().LoadConfiguration(builder =>
                {
                    // Configures logger to filter logs at Trace level and above and outputs them to a colored console.
                    builder.ForLogger().FilterMinLevel(LogLevel.Trace).WriteToColoredConsole();
                });

                // Initialize a new TxpServer instance listening on port 1151.
                TxpServer txpServer = new TxpServer(1151);

                // Subscribe to the OnPacketReceived event with an anonymous method to handle incoming packets.

                int vote_counter = 0;
                int unsatcount = 0;
                int satcount = 0;
                string filePath = @"C:\PipList\server_output.txt";

                txpServer.OnPacketReceived += (clientState, data) =>
                {
                    var receivedHeader = Header.FromBytes(data);

                    int connectedclients = txpServer.conversations.Count;
                    logger.Trace($"Received packet from CID {clientState.ConversationId} of type {receivedHeader.type}");

                    if (receivedHeader.type == PacketType.Hello)
                    {
                        HandleHelloPacket(txpServer, clientState, data);
                    }
                    else if (receivedHeader.type == PacketType.Vote_Request_Vote_C2S)
                    {
                        vote_counter = 0;
                        unsatcount = 0;
                        satcount = 0;
                        PipServer.PipServerBroadcastQuestion(txpServer, data);

                    }
                    else if (receivedHeader.type == PacketType.Vote_Answer_Vote_C2S)
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
                            final = PipServer.OrganizeData(txpServer, vote_counter, unsatcount, satcount);
                            Guid tempguid = voteresultpacket.GetGuid();
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
                };


                /*// Logs the receipt of a packet using Trace level, including the client's ID and the packet data as a hex string.
                logger.Trace($"Received packet from CID {clientState.ConversationId} with data: {}");

                // Checks if the received data matches a specific byte sequence.
                if (data.SequenceEqual(new byte[] { 0x01, 0x02, 0x03, 0x04 }))
                {
                    // Logs a Debug level message indicating a specific test packet was received.
                    logger.Debug("Received test packet 1, sending back 0x13 0x13 0x13 0x13");

                    // Prepares a response byte array to send back to the client.
                    byte[] response = new byte[] { 0x13, 0x13, 0x13, 0x13 };
                    // Sends the prepared response to the client who sent the original packet.
                    txpServer.Send(response, clientState);
                }*/

                // Starts the server to begin listening for incoming connections and packets.
                txpServer.Start();

                // Logs an Info level message indicating the server has started.
                logger.Info("Server started...");
            }
            catch (Exception ex)
            {
                // Logs any exceptions that occur during server setup or operation as Error level logs.
                logger.Error(ex, "An error occurred while running the server");
            }

            // Puts the main thread to sleep indefinitely, preventing the program from exiting.
            Thread.Sleep(-1);
        }
    }
    private static void HandleHelloPacket(TxpServer, TxpServer.ClientState clientState, byte[] data)
    {
        PacketHello helloPacket = PacketHello.FromBytes(data);
        Guid clientId = clientState.ConversationId;

        //adding client + features to dictionary
        clientFeatures[clientId] = helloPacket.GetFeatures(data);

        //response
        Header responseheader = new Header(PacketType.Hello);
        PacketHello repsonseHelloPacket = new PacketHello
        {
            responseheader = responseheader,
            version = helloPacket.version,
            numFeatures = (ushort)Enum.GetValues(typeof(Feature)).Length
        };

    StringBuilder featureMessage = new StringBuilder();
    featureMessage.Append("Hello, the server has these features: ");
    foreach(Feature feature in Enum.GetValues(typeof(Feature)))
        {
            featureMessage.Append(feature.ToString());
            featureMessage.Append(", ");
        }

    featureMessage.Remove(featureMessage.Length - 2, 2); //removing last ","

        //convert msg to bytes
        byte[] messageBytes = Enconding.UTF8.GetBytes(featureMessage.ToString());
        //serialize the response hello packet
        byte[] responseData = responseHelloPacket.Serialize(Enum.GetValues(typeof(Feature)) as feature[]);
        //array to hold the combined msg and pkt 
        byte[] combinedData = new byte[responseData.Length + messageBytes.Length];

        Array.Copy(responseData, 0, combinedData, 0, responseData.Length);
        Array.Copy(messageBytes, 0 , combinedData, responseData.Length, messageBytes.Length);

        Server.Send(combinedData, clientState);

    }
}
