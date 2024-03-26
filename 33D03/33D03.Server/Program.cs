
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
                txpServer.OnPacketReceived += (clientState, data) =>
                {
                    logger.Trace($"Received packet from CID {clientState.ConversationId} with data: {PacketRequestVote.FromBytes(data)}");
                    (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
                    string Guidss = recievedpacktestvote.Getguid();
                    Console.WriteLine(Guidss);
                    Console.WriteLine(recievedpacktestvote.GetLength());
                    Console.WriteLine(question);




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

                };

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
}
