using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using _33D03.Shared.Pip;
using NLog.LayoutRenderers;
using Microsoft.Z3;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using NLog;
using OneOf.Types;
using System.Data;

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
            int diffProblems = random.Next(1, 4);
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

        public static string GenerateEvalString()
        {
            StringBuilder evalString = new StringBuilder();
            string expression = "";
            string expression2 = "";

            int numOperands = random.Next(2, 11);

            for (int i = 0; i < numOperands; i++)
            {
                int operand = random.Next(-255, 255);
                expression += operand;

                if (i < numOperands - 1)
                {
                    char[] operators = { '+', '-', '*', '/' };
                    char operatorChar = operators[random.Next(operators.Length)];
                    expression += operatorChar;
                }
            }

            int numOperands2 = random.Next(2, 11);

            for (int i = 0; i < numOperands2; i++)
            {
                int operand2 = random.Next(-255, 255);
                expression2 += operand2;

                if (i < numOperands2 - 1)
                {
                    char[] operators = { '+', '-', '*', '/' };
                    char operatorChar = operators[random.Next(operators.Length)];
                    expression2 += operatorChar;
                }
            }

            bool generateSat = random.Next(0, 2) == 0;
            if (generateSat == true)
            {
                double result = EvaluateExpression(expression);
                evalString.Append($"{expression} == {Math.Round(result)}");
            }
            else
            {
                double result = random.Next(-255, 255);
                evalString.Append($"{expression} > {expression2}");
            }
            return evalString.ToString();
        }

        static double EvaluateExpression(string expression)
        {
            try
            {
                // DataTable.Compute returns an object, so we cast it to double
                return Convert.ToDouble(new System.Data.DataTable().Compute(expression, null));
            }
            catch
            {
                throw; // Re-throw the exception to be caught by the caller
            }
        }

        public static void VoteSimpleInit(TxpClient client)
        {
            var question = GenerateEvalString();
            var questionlength = (uint)question.Length;
            var header = new Header(PacketType.Vote_Request_Simple_C2S);
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

        public static void VoteSimpleTyped(TxpClient client)
        {
            string question = UI.VoteManUI();
            var questionlength = (uint)question.Length;
            var header = new Header(PacketType.Vote_Request_Simple_C2S);
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


        //called for each VOTEINIT by client, sends randomly generated question
        public static void Client_request_info(TxpClient client)
        {
            var header = new Header(PacketType.Client_request_info);
            var requestpacket = new ClientToServerRequestInfo(header);
            byte[] sendinforequestbytestream = requestpacket.serialize();
            Array.Reverse(sendinforequestbytestream);
            client.Send(sendinforequestbytestream);
            logger.Info($"Client Sent info request to server{BitConverter.ToString(sendinforequestbytestream)}");
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
            hellopacket.numFeatures = (ushort)features.Length;
            byte[] hellosendpacket = hellopacket.Serialize(features);
            return hellosendpacket;
        }

        public static void SendHello(TxpClient client, Feature[] features)
        {
            var header = new Header(PacketType.Hello_C2S);
            var hellopacket = new PacketHello(header);
            hellopacket.numFeatures = (ushort)features.Length;
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
            var result = SMTChecker(question);
            var Client_Answer_Packet = new PacketAnswerVote(header, voteGuid, result);
            Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
            Console.WriteLine("||                                                   This Client                                                 ||");
            if (Client_Answer_Packet.GetResponse() == VoteResponse.SAT)
            {
                Console.WriteLine("||                                                    Satisfied                                                  ||");
            }
            else if (Client_Answer_Packet.GetResponse() == VoteResponse.UNSAT)
            {
                Console.WriteLine("||                                                   Unsatisfied                                                 ||");
            }
            else Console.WriteLine("Syntax Error");
            byte[] answerinitbytes = Client_Answer_Packet.Serialize();
            client.Send(answerinitbytes);
            logger.Info("Client respond with " + Client_Answer_Packet.GetResponse() + "vote ID: " + voteGuid);
        }

        public static void ClientAnswerVoteSimple(TxpClient client, string question, Guid voteID)
        {
            var header = new Header(PacketType.Vote_answer_Simple_C2S);
            Guid voteGuid = voteID;
            var result = EvalChecker(question);
            var Client_Answer_Packet = new PacketAnswerVote(header, voteGuid, result);
            Console.WriteLine("||                                                   This Client                                                 ||");
            if (Client_Answer_Packet.GetResponse() == VoteResponse.SAT)
            {
                Console.WriteLine("||                                                    Satisfied                                                  ||");
            }
            else if (Client_Answer_Packet.GetResponse() == VoteResponse.UNSAT)
            {
                Console.WriteLine("||                                                   Unsatisfied                                                 ||");
            }
            else Console.WriteLine("Syntax Error");
            byte[] answerinitbytes = Client_Answer_Packet.Serialize();
            client.Send(answerinitbytes);
            logger.Info("Client respond with " + Client_Answer_Packet.GetResponse() + "vote ID: " + voteGuid);
        }

        public static VoteResponse EvalChecker(string question)
        {
            try
            {
                // Regular expression to identify comparison operators and split the expression accordingly
                Regex regex = new Regex(@"(==|<=|>=|<|>|=)");
                Match match = regex.Match(question);

                if (!match.Success || match.Groups.Count < 1)
                {
                    throw new ArgumentException("Invalid or missing comparison operator");
                }

                string operatorFound = match.Groups[0].Value;
                string[] parts = regex.Split(question, 2);

                string leftSide = parts[0].Trim();
                string rightSide = parts[2].Trim(); // parts[1] will be the operator, which we already have

                // Evaluate both sides
                DataTable dataTable = new DataTable();
                double leftResult = Convert.ToDouble(dataTable.Compute(leftSide, ""));
                double rightResult = Convert.ToDouble(dataTable.Compute(rightSide, ""));
                string leftResultStr = " Left Result: " + leftResult;
                string rightResultStr = " Right Result: " + rightResult;
                UI.PrintCenteredText(leftResultStr, 120);
                UI.PrintCenteredText(rightResultStr, 120);
                Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
                // Perform the comparison
                bool comparisonResult = operatorFound switch
                {
                    "<" => (int)leftResult < (int)rightResult,
                    ">" => (int)leftResult > (int)rightResult,
                    "<=" => (int)leftResult <= (int)rightResult,
                    ">=" => (int)leftResult >= (int)rightResult,
                    "==" => (int)leftResult == (int)rightResult,
                    "=" => (int)leftResult == (int)rightResult,
                    _ => throw new ArgumentException("no comparator found")
                };


                return (comparisonResult ? VoteResponse.SAT : VoteResponse.UNSAT);
            }
            catch (Exception)
            {
                return VoteResponse.UNKNOWN;
            }
        }

        public static VoteResponse SMTChecker(string question)
        {
            using Context z3Ctx = new Context();
            var model = z3Ctx.ParseSMTLIB2String(question);
            var solver = z3Ctx.MkSimpleSolver();
            solver.Assert(model);

            if (solver.Check() == Status.SATISFIABLE)
            {
                return VoteResponse.SAT;
            }
            else if (solver.Check() == Status.UNSATISFIABLE)
            {
                return VoteResponse.UNSAT;
            }
            else return VoteResponse.UNKNOWN;
        }

    }

    public class UI
    {
        internal static void PrintLOGO()
        {
            Console.WriteLine("                    ||                                                                       ||");
            Console.WriteLine("                    ||                    ,--.                    ,--.  ,--,------,--------. ||");
            Console.WriteLine("                    ||    ,--.  ,--,---.,-'  '-.,---.             |  ,'.|  |  .---'--.  .--' ||");
            Console.WriteLine("                    ||     \\  `'  | .-. '-.  .-| .-. :            |  |' '  |  `--,   |  |    ||");
            Console.WriteLine("                    ||      \\    /' '-' ' |  | \\   --.    .--.    |  | `   |  `---.  |  |    ||");
            Console.WriteLine("                    ||       `--'  `---'  `--'  `----'    '--'    `--'  `--`------'  `--'    ||");
            Console.WriteLine("                    ||                                                                       ||");
        }

        public static void StartupUIClient()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                                 33D03                               =||");
            Console.WriteLine("                    ||=                                Group 1                              =||");
            Console.WriteLine("                    ||=                       Press Enter to Continue                       =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.ReadLine();
        }



        public static void FeatureSelectUI()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                        0 - Simple Verification                      =||");
            Console.WriteLine("                    ||=                         1 - SMT Verification                        =||");
            Console.WriteLine("                    ||=                           2 - OCR Enabled                           =||");
            Console.WriteLine("                    ||=                                                                     =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void FeatureSelectInvalidUI()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                   Invalid Input, Please check again                 =||");
            Console.WriteLine("                    ||=                        0 - Simple Verification                      =||");
            Console.WriteLine("                    ||=                         1 - SMT Verification                        =||");
            Console.WriteLine("                    ||=                           2 - OCR Enabled                           =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void AddedFeature()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                             Added Feature                           =||");
            Console.WriteLine("                    ||=                        0 - Simple Verification                      =||");
            Console.WriteLine("                    ||=                         1 - SMT Verification                        =||");
            Console.WriteLine("                    ||=                           2 - OCR Enabled                           =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }



        public static void ServerConnected()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                            ServerConnected                          =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void InvalidInput()
        {
            Console.Clear();
            Console.WriteLine("                      ___ _   ___     ___    _     ___ ____    ___ _   _ ____  _   _ _____");
            Console.WriteLine("                     |_ _| \\ | \\ \\   / / \\  | |   |_ _|  _ \\  |_ _| \\ | |  _ \\| | | |_   _|");
            Console.WriteLine("                      | ||  \\| |\\ \\ / / _ \\ | |    | || | | |  | ||  \\| | |_) | | | | | |  ");
            Console.WriteLine("                      | || |\\  | \\ V / ___ \\| |___ | || |_| |  | || |\\  |  __/| |_| | | |  ");
            Console.WriteLine("                     |___|_| \\_|  \\_/_/   \\_|_____|___|____/  |___|_| \\_|_|    \\___/  |_|  ");
            Console.WriteLine("                                                                                            ");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                             Invalid Input                           =||");
            Console.WriteLine("                    ||=                        Press Enter to Continue                      =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.ReadLine();
        }

        public static void SelectFunction()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                        vote - Random SMT Vote                       =||");
            Console.WriteLine("                    ||=                     votesimple - Random Eval Vote                   =||");
            Console.WriteLine("                    ||=                          Info - get info list                       =||");
            Console.WriteLine("                    ||=                       voteman - manual eval vote                    =||");
            Console.WriteLine("                    ||=                                                                     =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
        }

        public static void PrintFeatureListUI(List<ServerListofClients> clients)
        {
            Console.Clear();
            Thread.Sleep(1);
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=                        vote - Random SMT Vote                       =||");
            Console.WriteLine("                    ||=                     votesimple - Random Eval Vote                   =||");
            Console.WriteLine("                    ||=                          Info - get info list                       =||");
            Console.WriteLine("                    ||=                       voteman - manual eval vote                    =||");
            Console.WriteLine("                    ||=                                                                     =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
            Console.WriteLine("||=                                                Feature List                                                 =||");
            foreach (var client in clients)
            {
                Console.WriteLine("||---------------------------------------------------------------------------------------------------------------||");
                Console.WriteLine($"||={client.convoid,-10} {client.numFeatures,-5} {client.features[0],-30} {client.features[1],-30} {client.features[2],-30}=||");
                Console.WriteLine("||---------------------------------------------------------------------------------------------------------------||");
            }
            Console.WriteLine("-------------------------------------------------------------------------------------------------------------------");
        }

        public static string VoteManUI()
        {
            Console.Clear();
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            PrintLOGO();
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ||=Enter Question:                                                      =||");
            Console.WriteLine("                    ||=======================================================================||");
            Console.WriteLine("                    ---------------------------------------------------------------------------");
            MoveCursorUpAndRight(3, 40);
            string question = Console.ReadLine();
            return question;
        }








        internal static void MoveCursorUpAndRight(int up, int right)
        {
            try
            {
                // Get current cursor position
                int currentLeft = Console.CursorLeft;
                int currentTop = Console.CursorTop;

                // Calculate new cursor position
                int newLeft = currentLeft + right;
                int newTop = currentTop - up;

                // Ensure the new position is within the console buffer
                newLeft = Math.Max(0, Math.Min(Console.BufferWidth - 1, newLeft));
                newTop = Math.Max(0, Math.Min(Console.BufferHeight - 1, newTop));

                // Set new cursor position
                Console.SetCursorPosition(newLeft, newTop);
            }
            catch (ArgumentOutOfRangeException e)
            {
                Console.WriteLine($"Error moving cursor: {e.Message}");
            }
        }

        public static void PrintCenteredText(string text, int lineWidth)
        {
            string[] words = text.Split(' ');
            string line = "";

            foreach (var word in words)
            {
                if ((line + word).Length > lineWidth)
                {
                    Console.WriteLine(CenterLine(line.Trim(), lineWidth));
                    line = word + " ";
                }
                else
                {
                    line += word + " ";
                }
            }
            if (line.Length > 0)
            {
                Console.WriteLine(CenterLine(line.Trim(), lineWidth));
            }
        }

        static string CenterLine(string line, int lineWidth)
        {
            int spacesToAdd = (lineWidth - line.Length) / 2;
            return new string(' ', spacesToAdd) + line;
        }
    }
}