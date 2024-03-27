﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public enum AckType
    {
        Ack,
        Nack
    }
    public enum AckAction
    {
        Continue,
        Rebroadcast
    }
    public class AckHandler
    {
        private UdpClient udpClient;
        private uint converstaionId;
        private AckType lastAckType;
        private AutoResetEvent ackReceivedEvent = new AutoResetEvent(false);

        public AckHandler(UdpClient udpClient, uint converstaionId)
        {
            this.udpClient = udpClient;
            this.converstaionId = converstaionId;
        }

        public void SpecifyAckReceived()
        {
            lastAckType = AckType.Ack;
            ackReceivedEvent.Set();
        }
        public void SpecifyNackReceived()
        {
            lastAckType = AckType.Nack;
            ackReceivedEvent.Set();
        }
        public AckAction WaitForAckOrTimeout()
        {
            if (ackReceivedEvent.WaitOne(TimeSpan.FromMilliseconds(Constants.ACK_TIMEOUT_MS)))
            {
                if (lastAckType == AckType.Ack)
                {   //Console.WriteLine("Ack SENT");
                    return AckAction.Continue;
                    
                }
                else
                {
                    return AckAction.Rebroadcast;
                }
            }

            return AckAction.Rebroadcast;
        }

        public void SendAck(uint sequenceNumber, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = converstaionId,
                seqNum = sequenceNumber,
                finish = 1,
                type = Shared.Txp.PacketType.ACK
            };

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
            //Console.WriteLine("ack RECIEVED");
        }

        public void SendNack(uint sequenceNumber, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = converstaionId,
                seqNum = sequenceNumber,
                finish = 1,
                type = Shared.Txp.PacketType.NACK
            };

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }
    }
}
