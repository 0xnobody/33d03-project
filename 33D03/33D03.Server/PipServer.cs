using NLog;
using System;
using System.Text;
using _33D03.Server;
using System.Security.Cryptography.X509Certificates;
using _33D03.Shared.Pip;

namespace _33D03.Server
{

    public struct ServerVoteLog
    {
        Guid servervoteguid;
        ushort result;

        public ServerVoteLog(Guid inputGuid, ushort rest)
        {
            servervoteguid = inputGuid;
            result = rest;
        }
        public Guid GetGuid(){
            return servervoteguid;
        }
        public ushort GetResult(){
            return result;
        }
    }

    
    public static class PipServer
    {

        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();
        internal static void PipServerBroadcastQuestion(TxpServer server, byte[] data)
        {
            (PacketRequestVote recievedpacktestvote, string question) = PacketRequestVote.Deserialize(data);
            var sendQuestion = question;
            var questionlength = (uint)question.Length;
            var headertoclient = new Header(PacketType.Vote_Broadcast_Vote_S2C);
            Guid voteGuid = Guid.NewGuid();
            var Vote_init_packet = new PacketBroadcastVote(headertoclient, voteGuid, questionlength);
            var voteinitbytes = Vote_init_packet.Serialize(question);
            foreach (var conversationEntry in server.conversations)
            {
                var conversation = conversationEntry.Value;
                server.Send(voteinitbytes, conversation);
                logger.Info("Client initiate vote requst with SMTLIB question" + question + "Generating Vote with ID " + voteGuid);
            }
        }

        struct questionID
        {

        }

        internal static ushort OrganizeData(TxpServer server, int satcount, int unsatcount, int total)
        {
            if (satcount > unsatcount) return 1;
            else if (satcount <= unsatcount) return 0;
            else return 2;
        }

        internal static void ServerCalculatesVotes()
        {



        }






    }
}