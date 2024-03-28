using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared.Pip;
using NLog.LayoutRenderers;
using Microsoft.Z3;
using System.Runtime.Serialization;
using NLog;

namespace _33D03.Client
{
    public static class PipClient
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        static Random random = new Random();

        // Generates a random SMT-LIB string representing a SAT or UNSAT problem
        static string GenerateSMTLIBString()
        {
            StringBuilder smtBuilder = new StringBuilder();
            // Start with setting the logic
            smtBuilder.Append("(set-logic QF_LIA) ");
            // Declare two integer constants
            smtBuilder.Append("(declare-const x Int) (declare-const y Int) ");
            // Decide randomly to generate a SAT or UNSAT expression
            bool generateSAT = random.Next(0, 2) == 0;
            if (generateSAT)
            {
                // Generate a likely SAT example
                int a = random.Next(1, 10);
                smtBuilder.AppendFormat("(assert (= x (+ y {0}))) ", a);
            }
            else
            {
                // Generate a likely UNSAT example
                smtBuilder.Append("(assert (= (- x y) (+ x (- y) 1))) ");
            }
            // Finish with checking satisfiability
            smtBuilder.Append("(check-sat)");
            return smtBuilder.ToString();
        }

        public static void SendHello(TxpClient client)
        {
            var header = new Header(PacketType.Hello_C2S);
            Feature[] features = { Feature.SMTVerificationFeature, Feature.TestFeatrue1, Feature.TestFeatrue2 };
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = features.Length;
            var hellosendpacket = hellopacket.Serialize(features);
            client.Send(hellosendpacket);
            logger.Info($"Client Sent hello to server with features {string.Join(", ", features)}");
        }

        public static void VoteInit(TxpClient client)
        {
            var question = GenerateSMTLIBString();
            var questionlength = (uint)question.Length;
            var header = new Header(PacketType.Vote_Request_Vote_C2S);
            Guid voteGuid = Guid.NewGuid();
            var Vote_init_packet = new PacketRequestVote(header, voteGuid, questionlength);
            var voteinitbytes = Vote_init_packet.Serialize(question);
            client.Send(voteinitbytes);
            logger.Info("Client initiate vote requst with SMTLIB question" + question);
        }

        public static void ClientAnswerVote(TxpClient client, string question, Guid voteID)
        {
            var header = new Header(PacketType.Vote_Answer_Vote_C2S);
            Guid voteGuid = voteID;
            uint result = SMTChecker(question);
            Guid newguid = Guid.NewGuid();
            var Client_Answer_Packet = new PacketAnswerVote(header, voteGuid, newguid, (ushort)result);
            if (Client_Answer_Packet.GetResponse() == 1)
            {
                Console.WriteLine("Satisfied");
            }
            else if (Client_Answer_Packet.GetResponse() == 0)
            {
                Console.WriteLine("Unsatisfied");
            }
            else Console.WriteLine("Syntax Error");
            byte[] answerinitbytes = Client_Answer_Packet.Serialize();
            client.Send(answerinitbytes);
            Console.WriteLine("NEW GUID FOR THIS CLIENT RESPONSE IS " + Client_Answer_Packet.GetNewGuid());
            logger.Info("Client respond with " + Client_Answer_Packet.GetResponse() + "vote ID: " + voteGuid);
        }

        public static ushort SMTChecker(string question)
        {
            using Context z3Ctx = new Context();
            var model = z3Ctx.ParseSMTLIB2String(question);
            var solver = z3Ctx.MkSimpleSolver();
            solver.Assert(model);

            if (solver.Check() == Status.SATISFIABLE)
            {
                return 1;
            }
            else if (solver.Check() == Status.UNSATISFIABLE)
            {
                return 0;
            }
            else return 2;
        }
    }
}