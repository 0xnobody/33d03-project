using NLog;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public delegate void MaxSYNAttemptsReached();

    public class SynHandler
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private UdpClient client;
        private IPEndPoint lastEndPoint;
        private uint convId;

        private Thread workerThread;
        private ManualResetEvent resetEvent;
        private int synAttempts = 0;
        private bool teardown = false;

        public event MaxSYNAttemptsReached OnMaxSYNAttemptsReached;

        public SynHandler(UdpClient client, IPEndPoint initialEndPoint, uint convId)
        {
            this.client = client;
            lastEndPoint = initialEndPoint;
            this.convId = convId;

            resetEvent = new ManualResetEvent(false);
            workerThread = new Thread(WorkerFunction);
            workerThread.Start();
        }

        ~SynHandler()
        {
            teardown = true;
            resetEvent.Set();
        }

        private void WorkerFunction()
        {
            while (!teardown)
            {
                // Wait for the event to be set or the timeout to expire
                if (resetEvent.WaitOne(Constants.SYN_TIMEOUT_MS))
                {
                    // The event was set, reset it and continue waiting
                    resetEvent.Reset();
                }
                else
                {
                    if (synAttempts >= Constants.SYN_MAX_ATTEMPTS)
                    {
                        // Maximum number of attempts reached, reset the event and exit the loop
                        resetEvent.Reset();
                        synAttempts = 0;
                        OnMaxSYNAttemptsReached();

                        return;
                    }

                    // Timeout occurred, execute the function
                    SendSYN();
                    synAttempts++;
                }
            }
        }

        private void SendSYN()
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = convId,
                seqNum = 0,
                pcktNum = 0,
                finish = 0,
                type = Shared.Txp.PacketType.SYN
            };

            logger.Info($"Sending SYN with CID {convId}, {Shared.Txp.PacketType.SYN}");

            byte[] ackPacket = header.ToBytes();
            client.Send(ackPacket, ackPacket.Length, lastEndPoint);
        }
        public void RefreshSYNTimeout(IPEndPoint lastEndPoint)
        {
            this.lastEndPoint = lastEndPoint;
            resetEvent.Set();
            synAttempts = 0;
        }

        public void RespondToSYN(IPEndPoint endPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = convId,
                seqNum = 0,
                pcktNum = 0,
                finish = 0,
                type = Shared.Txp.PacketType.SYN_ACK
            };

            logger.Info($"Sending SYN ACK with CID {convId}");

            byte[] ackPacket = header.ToBytes();
            client.Send(ackPacket, ackPacket.Length, endPoint);
        }

        public void SYNACKReceived()
        {
            resetEvent.Reset();
            synAttempts = 0;
        }
    }
}
