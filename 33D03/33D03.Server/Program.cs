
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
using System.Formats.Asn1;
using Tensorflow.Keras.Layers;
using Microsoft.ML;

namespace _33D03.Server
{
    internal class Program
    {
        // Creates a logger instance for this class using NLog.
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

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
                TxpServer txpServer = new TxpServer(8080);
                List<ServerListofClients> ServerclientsList = new List<ServerListofClients>();
                List<ServerVoteId> ServerActiveQuestionList = new List<ServerVoteId>();

                Feature[] ServerFeatures = { Feature.SMTVerificationFeature, Feature.SimpleVerificationFeature, Feature.OCRFeature };
                ServerclientsList.Add(new ServerListofClients(0, 3, ServerFeatures));
                // Subscribe to the OnPacketReceived event with an anonymous method to handle incoming packets.

                string filePath = @"C:\PipList\server_output.txt";

                txpServer.OnPacketReceived += (clientState, data) =>
                {
                    OnPacketRecievedHandler(data, txpServer, clientState, ServerclientsList, ref ServerActiveQuestionList, filePath);
                };
                txpServer.OnClientDisconnected += (conversation) =>
                {
                    PipServer.ClientDisconnected(conversation, ServerclientsList, txpServer);
                };

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
        //handles what happeens when packets are recieved
        public static void OnPacketRecievedHandler(byte[] data, TxpServer txpServer, TxpClientConversation clientState, List<ServerListofClients> ServerclientsList, ref List<ServerVoteId> ServerActiveQuestionList, string filePath)
        {
            var receivedHeader = Header.FromBytes(data);

            int connectedclients = txpServer.conversations.Count;
            logger.Trace($"Received packet from CID {clientState.ConversationId} of type {receivedHeader.type}");
            if (receivedHeader.type == PacketType.Hello_C2S)
            {
                PipServer.HelloRecieved(txpServer, clientState, ServerclientsList, data, clientState.ConversationId);
                PipServer.SendInfo(txpServer, clientState, ServerclientsList, data, clientState.ConversationId);
            }
            else if (receivedHeader.type == PacketType.Client_request_info)
            {
                PipServer.SendInfo(txpServer, clientState, ServerclientsList, data, clientState.ConversationId);
            }
            else if (receivedHeader.type == PacketType.Vote_Request_Vote_C2S)
            {
                PipServer.SendInfo(txpServer, clientState, ServerclientsList, data, clientState.ConversationId);
                PipServer.PipServerBroadcastQuestion(txpServer, data, ServerActiveQuestionList, ServerclientsList);
            }
            else if (receivedHeader.type == PacketType.Vote_Request_Simple_C2S)
            {
                PipServer.PipServerBroadcastSimpleQuestion(txpServer, data, ServerActiveQuestionList, ServerclientsList);
            }
            else if (receivedHeader.type == PacketType.Vote_Answer_Vote_C2S)
            {
                PipServer.handlingvoteresults(txpServer, ref ServerActiveQuestionList, data, filePath);
            }
            else if (receivedHeader.type == PacketType.Vote_answer_Simple_C2S)
            {
                PipServer.handlingvoteresults(txpServer, ref ServerActiveQuestionList, data, filePath);
            }
        }

    }

}


