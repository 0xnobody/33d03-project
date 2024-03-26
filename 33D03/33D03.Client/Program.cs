using NLog;
using System;
using System.Collections.Generic;
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

        public static void ProcessInput(object obj)
        {
        if (obj is TxpClient client) // Check if obj is of type TxpClient and cast it
        {
            string inputstr = null;
            do{   
                inputstr = Console.ReadLine();
                if (inputstr == "InitVote"){
                    PipClient.VoteInit(client); // Assuming PipClient is a class or static method where VoteInit is defined
                    
                }
            }
            while (inputstr != "exit");
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
                    logger.Trace($"Received packet from Server with data: {PacketBroadcastVote.Deserialize(data)}");
                    (PacketBroadcastVote recievedBroadcastPacket, string question) = PacketBroadcastVote.Deserialize(data);
                    PacketType headerType = recievedBroadcastPacket.HeaderInfo.type;
                    ushort haedertypeshort = (ushort)headerType;
                    Console.WriteLine("header type is " + haedertypeshort);
                    if(haedertypeshort==3){
                        Console.WriteLine("Solving for smtlib question" + question);
                        PipClient.ClientAnswerVote(client, question);
                    }
                };

                

                client.Start();
                Thread write = new Thread(new ParameterizedThreadStart(ProcessInput));
                write.Start(client);

                //PipClient.VoteInit(client);

                
            }
            catch (Exception ex)
            {
                logger.Error(ex, "An error occurred while running the client");
            }

            Thread.Sleep(-1);
        }
    }
}
