using Nlog;
using System;
using System.Text;
using _33D03.Server;

internal class ServerPIP
{
    private TxpServer txpServer;

    private int satResults = 0;
    private int unsatResults = 0;
    private int totalClients = 0;
    private int timeouts = 0;
    private int syntaxErrors = 0;
    private int responses = 0;
    private double calculation = 0;
    private string result;
    private Random random = new Random();
    private static Logger logger = LogManager.GetCurrentClassLogger();

    public ServerPIP(TxpServer txpServer)
    {
        this.txpServer = txpServer;
    }

    public void Start()
    {
        txpServer.OnPacketReceived += TxpServer_OnPacketReceived;
        txpServer.Start();
        ServerVoteInitHandler();
    }

    private void TxpServer_OnPacketReceived(TxpClientConversation clientconversation, byte[] data)
    {
        string resp = Encoding.UTF8.GetString(data);
        logger.Info($"Receoved response from client {clientconversation.LastEndPoint}: {resp}");

        ProcessResp(resp);
    }

    private void ServerVoteInitHandler(TxpServer server)
    {
        string problem = ProblemGeneration(); //generate a random prob
        byte[] problemToSend = Encoding.UF8.GetBytes(problem); //convert from string to bits
        txpServer.send(problemToSend, clientStatus); //send packet in bits
        logger.Info($"Sent Problem to clients: {problem}");
    }

    //function to generate problems with random operands and aperators of different lenghts in SMT format
    static string ProblemGeneration()
    {

        int numOperands = random.Next(2, 10); //randomly generate number of operands between 2 and 9
        List<int> operands = new List<int>(); //list to store operands
        List<string> operators = new List<string>();//list to store operators

        //Generate and store operands
        for (int i = 0; i < numOperands; i++)
        {
            operands.Add(random.Next(-255, 255)); //randomly generate operands
        }

        for (int i = 0; i < numOperands - 1; i++)
        {
            string[] operators = { "+", "-", "*", "/" };
            string selectedOp = operators[random.Next(operators.Length)];
            operands.Add(selectedOp); //add selected operators to the list
        }
        StringBuilder equationBuilder = new StringBuilder();
        equationBuilder.Append("(assert ");
        for (int i = 0; i < numOperands - 1; i++)
        {
            equationBuilder.Append("(");
            equationBuilder.Append(operators[i]);
            equationBuilder.Append(" ");
            equationBuilder.Append(operands[i]);
            equationBuilder.Append(" ");
            equationBuilder.Append(operands[i+1]);
            equationBuilder.Append(")");
        }
        equationBuilder.Append(")");

        //calculate the total of the equation
        int total = operands[0];
        for (int i = 0; i < numOperands - 1; i++)
        {
            int operand = operands[i + 1];
            string op = operators[i];
            switch (op)
            {
                case "+":
                    total += operand;
                    break;
                case "-":
                    total -= operand;
                    break;
                case "*":
                    total *= operand;
                    break;
                case "/":
                    if (operand != 0)
                    {
                        total /= operand;
                    }
                    else
                    {
                        total += random.Next(-10, 10) + 1; //choose a non-zero operand (this will cause the clients to return unsat as they will deal with this issue in dif ways
                    }
                    break;
            }
        }
        equationBuilder.Append("(ssert (= result ");
        equationBuilder.Append(total);
        equationBuilder.Append("))");

        return equationBuilder.ToString();
    }

    private void ProcessResp(string resp)
    {
        if (resp.ToLower() == "satisfied")
        {
            satResults++;
        }
        else if (resp.ToLower() == "unstatisfied")
        {
            unsatResults++;
        }
        else if (resp.ToLower() == "timeout")
        {
            timeouts ++;
        }
        else if (resp.ToLower() == "sytax error")
        {
            syntaxErrors++;
        }

        responses++; //increase resp counter

        if (responses == totalClients)
        {
            calculateResult();
        }
        //This is to reduce the amount of time that the server has to wait if there is already an uncontested winner
        else if (responses < totalClients)
        {
            if (satResults > (totalClients / 2))
            {
                result = "Satisfied";
            }
            else if (unsatResults > (totalClients / 2))
            {
                result = "Unsatisfied";
            }
        }
    }

    private void calculateResult()
    {
        int ratio = satResults / totalClients;
        if (ratio > totalClients / 2)
        {
            result = "Satisfied";
        }
        else if (ratio < totalClients / 2)
        {
            result = "Unstatisfied";
        }
        else if (ratio == totalClients / 2)
        {
            result = "A TIE??";
        }
    }
}
