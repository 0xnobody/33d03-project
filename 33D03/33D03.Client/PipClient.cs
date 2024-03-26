using Microsoft.Z3;
using System;
using System.Text;
using System.Threading;

namespace _33D03.client
{
    public class ClientPIP
    {
        private TxpClient txpClient;
        private Context z3Context;

        public ClientPIP(TxpClient txpClient)
        {
            this.txpClient = txpClient;
            this.txpClient.OnPacketReceived += txpClient_OnPacketReceived;
            z3Context = new Context();
        }
        public void Start()
        {
            txpClient.Start();
        }
        private void TxpClient_OnPacketReceived(byte[] data)
        {
            string equation = Encoding.UTF8.GetString(data);
            Console.WriteLine($"Received equation: {equation}");

            string response;
            try
            {
                bool isSatisfied = SolveEquation(equation, out long elapsedMilliseconds);

                if (isSatisfied)
                {
                    response = "satisfied";
                }
                else
                {
                    response = "unsatisfied";
                }
                if (elapsedMilliseconds > 5000) 
                {
                    response = "timeout";
                }
            }
            catch (Z3Exception)
            {
                repsonse = "syntax_error";
            }
            txpClient.Send(Encoding.UTF8.GetBytes(response));
            Console.WriteLine("Sent '{response}' response to server.");
        }

        private bool SolveEquation(string equation)
        {
            Solver solver = z3Context.MkSolver();
            elaspedMilliseconds = 0;

            using (var timer = new Timer(state => solver.Interrupt()))
            {
                timer.Change(5000, Timeout.Infinite);
                DateTime startTime = DateTime.Now;

                //equation is already formated on arrival
                solver.Assert(z3Context.ParseSMTLIB2String(equation, null, null, null));

                Status status = solver.Check();
                DateTime endTime = DateTime.Now;

                elapsedMilliseconds = (long)(endTime - startTime).TotalMilliseconds;
                if (status = status.SATISFIABLE)
                {
                    return true;
                }
                else { return false; }
            }
        }
    }
}
