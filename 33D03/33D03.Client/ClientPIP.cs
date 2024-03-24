using _33D03.Client;
using NLog;
using System;
using System.Data;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;
using NLog.LayoutRenderers;

namespace _33d03.ClientPIP
{

    public class PIP{

        private string senddata = "33D03_client_initiate_vote"; //inital string converetd to bytes, check for successful conversion & if data in server reads, branch to server vote init handler
        public void Init_vote(TxpClient client){
            byte[] data = StrToByte(senddata);      //converts data string to bytes, using UTF8. Serialization needs to be completed.
            client.Send(data);                      //assuming ACK was implemented already in server send and client send TXP
        }


        //If we want to use this for checking file integrety, maybe we can use server side checksum vs client side checksum using SMT, and determine which files are corrupt?
        private static string StrToProblem(string problem){    
            var sides = problem.Split('=');         //Split our input into 2 sides
            if (sides.Length != 2) return "UNSAT";    //if there are no 2 sides, we return UNSAT and send to server
            string left_side = sides[0].Trim();         //left side trim all null
            string right_side = sides[1].Trim();        //right side trim all null
            var left_result = EvalStrProb(left_side);   //evaluate left side
            var right_result = EvalStrProb(right_side); //evaluate right side
            
            if (left_result == right_result){           //if no problem with equation, we return satisfied
                return "SAT";
            }
            else return "UNSAT";                        //otherwise we return unsatisfied
        }

        //evaluates string problem
        private static double EvalStrProb(string problem){
            object x = 0;       //declaring object x
            x = new DataTable().Compute(problem, null); //using datatable to solve our problem
            return Convert.ToDouble(x);                 //returns a double
        }

        public void ClientProblemHandler(TxpClient client, string problem){
            string VoteOutcome = StrToProblem(problem);
            client.Send(StrToByte(VoteOutcome));
        }

        public bool UpdateStatus(bool isSat, string ServerVoteOutcome){
            if(ServerVoteOutcome == "SAT"){
                isSat = true;
            } else if (ServerVoteOutcome == "UNSAT"){
                isSat = false; 
            }
            return isSat;
        }

        public static byte[] StrToByte(string str){ //basic method to convert strings to bytes using UTF8 encrpytion
            byte[] StrInByte;
            StrInByte = System.Text.Encoding.UTF8.GetBytes(str);
            return StrInByte;
        }

    }


































}