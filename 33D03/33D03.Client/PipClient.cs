using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared.Pip;
using NLog.LayoutRenderers;

namespace _33D03.Client
{
    public static class PipClient
    {
        public static void VoteInit(TxpClient client)
            {
                var header = new Header(PacketType.Vote_Request_Vote_C2S);
                Guid voteGuid = Guid.NewGuid();
                var Vote_init_packet = new PacketRequestVote(header, voteGuid, 100);
                byte[] voteinitbytes = Vote_init_packet.ToBytes();
                client.Send(voteinitbytes);
            }

        public static void ClientAnswerVote(TxpClient client){

        }

    }

    
}
