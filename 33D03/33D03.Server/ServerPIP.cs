using _33D03.Server;
using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography.X509Certificates;
using System.Text;
using System.Threading.Tasks;

public class ServerPIP{

    public Random random = new Random();
    
    private int result_Sat_Consensus = 0;
    private int result_Unsat_Consensus = 0;
    private int total_client = 0;

    public string ProblemGeneration(){  //randomely generates SMT equations
        string[] operators = { "+", "-", "*", "/" };
        int num1 = random.Next(-255, 255);
        int num2 = random.Next(-255, 255);
        int num3 = random.Next(-255, 255);
        int num4 = random.Next(-255, 255); 
        string op1 = operators[random.Next(operators.Length)];
        string op2 = operators[random.Next(operators.Length)];
        string eq = $"{num1} {op1} {num2} = {num3} {op2} {num4}";
        return eq;
    }

    internal void ServerVoteInitHandler(TxpServer server){
        string problemstr = ProblemGeneration();
        byte [] problembytes = StrToByte(problemstr);
        server.ServerBroadcast(problembytes);
    }

    public static byte[] StrToByte(string str){ //basic method to convert strings to bytes using UTF8 encrpytion
            byte[] StrInByte;
            StrInByte = System.Text.Encoding.UTF8.GetBytes(str);
            return StrInByte;
        }



























}