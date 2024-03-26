using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Client
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

                TxpClient client = new TxpClient("127.0.0.1", 1151);

                client.OnPacketReceived += (data) =>
                {
                    logger.Info($"Received packet: {BitConverter.ToString(data)}");
                };

                client.Start();

                PipClient.VoteInit(client);

                //return;

                //client.Send(new byte[] { 0x05, 0x06, 0x07, 0x08 });

                /*var bigData = new byte[1024];
                for (int i = 0; i < bigData.Length; i++)
                {
                    bigData[i] = (byte)i;
                }

                client.Send(bigData); */
            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the client");
            }

            Thread.Sleep(-1);
        }
    }
}
