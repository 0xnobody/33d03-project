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
            string[] diffLogics = new string[] { "QF_LIA" };           //chooses linear arithmetic as logic fragment (could add more such as QF_BV)
            string selectedLogic = diffLogics[random.Next(diffLogics.Length)];

            smtBuilder.AppendFormat("(set-logic {0})\n", selectedLogic);
            smtBuilder.Append("(declare-const x Int) (declare-const y Int) (declare-const z Int)\n");   //declaring 3 constants to be used in the expressions

            List<string> diffExpressions = new List<string>         //creates a list of 10 different expressions to be used
            {
                $"(= (+ x y) z)",                               //x + y = z
                $"(> x (* y 2))",                               //x > 2y
                $"(< (- x y) 5)",                               //x - y > 5
                $"(>= z (+ x 3))",                              //x + 3 <= z
                $"(distinct x y z)",                            //all 3 variables are different              
                $"(and (> x -5) (< y -10) (>= z (* x 2)))",     //all 3 conditions must be true due to and operator, x > -5, y > -10, z >2x
                $"(or (<= x y) (> z 10))",                      //either x <= y or z > 10 have to be true
                $"(not (= z (* x y)))",                         //will only be true if the condition is false, x * y = z
                $"(= (* x 3) (+ y (* z 2)))",                   //3x = 2z + y
                $"(<= (+ x y z) 100)"                           //all 3 variables must be less than or equal to 100
            };

            int randVal = random.Next(1, 11);   //picks random val between 1 and 10
            int numExpressions = randVal;       //uses the value to pick an amount of the expressions to be used in the smt problem for more variety

            var shuffled = diffExpressions.OrderBy(a => random.Next());     //shuffles up order of expressions for more variety
            diffExpressions = shuffled.ToList();

            for (int i = 0; i < numExpressions; i++)
            {
                smtBuilder.AppendFormat("(assert {0})\n", diffExpressions[i]);  //puts all of the expressions together to create final problem
            }

            // Finish with checking satisfiability
            smtBuilder.Append("(check-sat)");
            return smtBuilder.ToString();
        }


        //called for each VOTEINIT by client, sends randomly generated question
        public static void Client_request_info(TxpClient client)
        {
            var header = new Header(PacketType.Client_request_info);
            var requestpacket = new ClientToServerRequestInfo(header);
            byte[] sendinforequestbytestream = requestpacket.serialize();
            client.Send(sendinforequestbytestream);
            logger.Info($"Client Sent info request to server");
        }

        //gets info request bytes, reduces calculation when needed for flooding
        public static byte[] GetinfoBytes()
        {
            var header = new Header(PacketType.Client_request_info);
            var requestpacket = new ClientToServerRequestInfo(header);
            byte[] sendinforequestbytestream = requestpacket.serialize();
            return sendinforequestbytestream;
        }

        //gests hello bytes, see how server responds.
        public static byte[] GethelloBytes()
        {
            var header = new Header(PacketType.Hello_C2S);
            Feature[] features = { Feature.SimpleVerificationFeature, Feature.SMTVerificationFeature, Feature.OCRFeature };
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = features.Length;
            byte[] hellosendpacket = hellopacket.Serialize(features);
            return hellosendpacket;
        }

        public static void SendHello(TxpClient client)
        {
            var header = new Header(PacketType.Hello_C2S);
            Feature[] features = { Feature.SimpleVerificationFeature, Feature.SMTVerificationFeature, Feature.OCRFeature };
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = features.Length;
            byte[] hellosendpacket = hellopacket.Serialize(features);
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
