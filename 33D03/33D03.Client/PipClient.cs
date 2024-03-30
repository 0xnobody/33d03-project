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


        //
        //  dont use right now, crashes
        //
        static string GenerateSMTLIBStringMoreOptions()
        {
            StringBuilder smtBuilder = new StringBuilder();
            string[] diffLogics = new string[] { "QF_LIA", "QF_BV" };           //randomises the logic used between linear integer arithmetic or bit vectors
            string selectedLogic = diffLogics[random.Next(diffLogics.Length)];

            smtBuilder.Append($"(set-logic {selectedLogic})\n");

            //declares constants based off selected logic
            if (selectedLogic == "QF_LIA")
            {
                smtBuilder.Append("(declare-const x Int) (declare-const y Int)\n");
            }
            else if (selectedLogic == "QF_BV")
            {
                smtBuilder.Append("(declare-const a (_ BitVec 32)) (declare-const b (_ BitVec 32))\n");
            }

            //randomises type of SMT problem created by the generator
            //should produce mix of SAT and UNSAT
            int diffProblems = random.Next(1,4);
            if (diffProblems == 0)
            {
                int randVal = random.Next(-255, 255);
                if (selectedLogic == "QF_LIA")  //these comparisons will likely be SAT
                {
                    smtBuilder.AppendFormat("(assert (> (+ x y) {0}))\n", randVal);
                }
                else if (selectedLogic == "QF_BV")
                {
                    smtBuilder.AppendFormat("(assert (bvslt (bvadd a b) #x{0:X8}))\n", randVal);
                }
            }
            else if (diffProblems == 1)         //these logical expressions should also likely be SAT
            {
                if (selectedLogic == "QF_LIA")
                {
                    smtBuilder.AppendLine("(assert (or (> x 1) (< y 15)))");
                }
                else
                {
                    smtBuilder.AppendLine("(assert (bvor (bvslt a #x0000000A) (bvsgt b #x000000AA)))");
                }
            }
            else if (diffProblems == 2)         //these conditions should always be UNSAT as there is no constant values that should satisfy
            {
                if (selectedLogic == "QF_LIA")
                {
                    smtBuilder.AppendLine("(assert (and (> x 70) (< x 40)))");
                }
                else
                {
                    smtBuilder.AppendLine("(assert (and (bvslt a #x00000044) (bvsgt a #x00000067)))");
                }
            }
            else if (diffProblems == 3)         //more conditions that will likely be SAT that include some multiplication and addition
            {
                if (selectedLogic == "QF_LIA")
                {
                    smtBuilder.AppendLine("(assert (= (+ x (* 2 y)) 50))");
                }
                else
                {
                    smtBuilder.AppendLine("(assert (bvsle (bvadd a b) #xF000000F))");
                }
            }

            // Finish with checking satisfiability
            smtBuilder.Append("(check-sat)");
            return smtBuilder.ToString();
        }


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


        //called for each VOTEINIT by client, sends randomly generated question
        public static void Client_request_info(TxpClient client){
            var header = new Header(PacketType.Client_request_info);
            var requestpacket = new ClientToServerRequestInfo(header);
            byte [] sendinforequestbytestream = requestpacket.serialize();
            client.Send(sendinforequestbytestream);
            logger.Info($"Client Sent info request to server");
        }

        //gets info request bytes, reduces calculation when needed for flooding
        public static byte [] GetinfoBytes(){
            var header = new Header(PacketType.Client_request_info);
            var requestpacket = new ClientToServerRequestInfo(header);
            byte [] sendinforequestbytestream = requestpacket.serialize();
            return sendinforequestbytestream;
        }

        //gests hello bytes, see how server responds.
        public static byte [] GethelloBytes(){
            var header = new Header(PacketType.Hello_C2S);
            Feature [] features = {Feature.SMTVerificationFeature, Feature.TestFeatrue1, Feature.TestFeatrue2};
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = features.Length;
            byte [] hellosendpacket = hellopacket.Serialize(features);
            return hellosendpacket;
        }

        public static void SendHello(TxpClient client){
            var header = new Header(PacketType.Hello_C2S);
            Feature [] features = {Feature.SMTVerificationFeature, Feature.TestFeatrue1, Feature.TestFeatrue2};
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = features.Length;
            byte [] hellosendpacket = hellopacket.Serialize(features);
            client.Send(hellosendpacket);
            logger.Info($"Client Sent hello to server with features {string.Join(", ",features)}");
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
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            logger.Info("Client initiate vote requst with SMTLIB question" + question);
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
        }

        public static void ClientAnswerVote(TxpClient client, string question, Guid voteID)
        {
            var header = new Header(PacketType.Vote_Answer_Vote_C2S);
            Guid voteGuid = voteID;
            uint result = SMTChecker(question);
            Guid newguid = Guid.NewGuid();
            var Client_Answer_Packet = new PacketAnswerVote(header, voteGuid,newguid, (ushort)result);
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
            Console.WriteLine("NEW GUID FOR THIS CLIENT RESPONSE IS "+ Client_Answer_Packet.GetNewGuid());
            logger.Info("Client respond with " + Client_Answer_Packet.GetResponse() + "vote ID: " +voteGuid);
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