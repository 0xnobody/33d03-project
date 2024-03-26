using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Server
{
    internal class Program
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private static void Main(string[] args)
        {
            try
            {
                // Setup logging
                NLog.LogManager.Setup().LoadConfiguration(builder =>
                {
                    builder.ForLogger().FilterMinLevel(LogLevel.Trace).WriteToColoredConsole();
                });

                TxpServer txpServer = new TxpServer(1151);

                txpServer.OnPacketReceived += (clientState, data) =>
                {
                    logger.Trace($"Received packet from CID {clientState.ConversationId} with data: {BitConverter.ToString(data)}");

                    if (data.SequenceEqual(new byte[] { 0x01, 0x02, 0x03, 0x04 }))
                    {
                        logger.Debug("Received test packet 1, sending back 0x13 0x13 0x13 0x13");

                        byte[] response = new byte[] { 0x13, 0x13, 0x13, 0x13 };
                        txpServer.Send(response, clientState);
                    }
                };

                txpServer.Start();

                logger.Info("Server started...");

            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the server");
            }

            Thread.Sleep(-1);
        }
    }
}
