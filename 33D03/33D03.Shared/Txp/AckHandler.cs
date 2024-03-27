using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;
using NLog;

namespace _33D03.Shared.Txp
{
    public enum AckAction
    {
        Continue,
        Rebroadcast
    }
    public class AckHandler
    {
        private UdpClient udpClient;
        private uint converstaionId;
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        public AckHandler(UdpClient udpClient, uint converstaionId)
        {
            this.udpClient = udpClient;
            this.converstaionId = converstaionId;
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

            logger.Info("Sending ACK with sn " + sequenceNumber);

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
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

            logger.Info("Sending NACK with sn " + sequenceNumber);

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }

        public Shared.Txp.AckAction ListenForAck(ref IPEndPoint remoteEndPoint)
        {
            var pckt = Shared.Txp.Interface.ListenForPacket(udpClient, ref remoteEndPoint, TimeSpan.FromMilliseconds(Shared.Txp.Constants.ACK_TIMEOUT_MS));
            if (pckt == null)
            {
                logger.Warn("Timout occurred");
                return Shared.Txp.AckAction.Rebroadcast;
            }

            if (pckt.Item1.type == Shared.Txp.PacketType.Data)
            {
                logger.Warn("Received data packet where ACK/NACK was expected");
            }

            if (pckt.Item1.type == Shared.Txp.PacketType.ACK)
            {
                return Shared.Txp.AckAction.Continue;
            }

            return Shared.Txp.AckAction.Rebroadcast;
        }
    }
}
