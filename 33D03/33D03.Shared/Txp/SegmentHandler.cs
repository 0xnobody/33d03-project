using System;
using System.Collections.Generic;
using System.Linq;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    /// <summary>
    /// Handles the segmentation and recombination of packets.
    /// </summary>
    public class SegmentHandler
    {
        private static NLog.Logger logger = NLog.LogManager.GetCurrentClassLogger();

        private UdpClient udpClient;
        private uint conversationId;

        /// <summary>
        /// A dictionary of incoming segments, indexed by sequence number.
        /// </summary>
        public Dictionary<uint, byte[]> IncomingSegments = new Dictionary<uint, byte[]>();

        /// <summary>
        /// Index of the current expected incoming packet. Incremented when a full packet is reassembled.
        /// </summary>
        public uint IncomingPacketIndex = 0;

        /// <summary>
        /// A dictionary of outgoing segments, indexed by sequence number.
        /// </summary>
        public Dictionary<uint, byte[]> OutgoingSegments = new Dictionary<uint, byte[]>();

        /// <summary>
        /// List of sequence numbers for the segments that have been acknowledged.
        /// </summary>
        public List<uint> IncomingSegmentAcks = new List<uint>();

        /// <summary>
        /// Was the incoming finish segment received?
        /// </summary>
        public bool IncomingFinished = false;

        /// <summary>
        /// For the current outgoing packet, the number of segments (or highest segment number) that need to be acknowledged.
        /// </summary>
        public uint NumberOfSegmentsToAck;

        /// <summary>
        /// Index of the current outgoing packet. Incremented when all segments of a packet have been acknowledged.
        /// </summary>
        public uint OutgoingPacketIndex = 0;

        /// <summary>
        /// A queue of outgoing packets that are waiting to be sent. Packets must wait until all segments of the previous packet have been acknowledged.
        /// </summary>
        public Queue<byte[]> OutgoingPacketQueue = new Queue<byte[]>();

        /// <summary>
        /// Determines whether the handler is ready to send the next outgoing packet, i.e. all segments of the previous packet have been acknowledged.
        /// </summary>
        public bool ReadyForNextOutgoingPacket = true;

        public Mutex PacketQueueMutex = new Mutex();

        public SegmentHandler(UdpClient client, uint convId)
        {
            udpClient = client;
            conversationId = convId;
        }

        /// <summary>
        /// Sends the provided segment to the specified endpoint. If the segment is not acknowledged within a timeout, a NACK is sent.
        /// </summary>
        /// <param name="seqNum"></param>
        /// <param name="pcktNum"></param>
        /// <param name="endPoint"></param>
        private void sendSegment(uint seqNum, uint pcktNum, IPEndPoint endPoint)
        {
            logger.Info($"Sending segment {seqNum}:{pcktNum}");

            udpClient.Send(OutgoingSegments[seqNum], endPoint);

            // If the segment is not acknowledged within a timeout, resend it
            //
            uint packetIndex = OutgoingPacketIndex;
            Task.Delay(Shared.Txp.Constants.ACK_TIMEOUT_MS).ContinueWith((Task task) =>
            {
                //
                // TODO: do we need to acquire packet queue mutex here?
                // We might have a race condition with OutgoingPacketIndex here.
                //

                // If the packet index has changed, we have moved on to the next packet and should not resend it.
                // This would occur if the client resent the previous packet after we moved on to the next packet.
                //
                if (packetIndex == OutgoingPacketIndex)
                {
                    if (!IncomingSegmentAcks.Contains(seqNum))
                    {
                        sendSegment(seqNum, pcktNum, endPoint);
                    }
                }
            });
        }

        /// <summary>
        /// Splits a packet into segments and sends them to the specified endpoint. This should only be called when the handler is ready to send the next packet.
        /// </summary>
        /// <param name="data"></param>
        /// <param name="endPoint"></param>
        private void sendPacket(byte[] data, IPEndPoint endPoint)
        {
            // Split the packet into segments.
            //
            OutgoingSegments = Shared.Txp.Interface.SerializeData(data, OutgoingPacketIndex, conversationId, ref NumberOfSegmentsToAck);

            foreach (var segment in OutgoingSegments)
            {
                sendSegment(segment.Key, OutgoingPacketIndex, endPoint);
            }
        }

        /// <summary>
        /// Sends the provided data to the specified endpoint. If the handler is not ready to send the next packet, the data is queued.
        /// In this case, the packet will be sent when the SendNextPacket function is called, i.e. when all segments of the previous packet have been acknowledged.
        /// </summary>
        /// <param name="data"></param>
        /// <param name="endPoint"></param>
        public void SendOrQueuePacket(byte[] data, IPEndPoint endPoint)
        {
            lock (PacketQueueMutex)
            {
                if (ReadyForNextOutgoingPacket)
                {
                    sendPacket(data, endPoint);
                }
                else
                {
                    OutgoingPacketQueue.Enqueue(data);
                }

                ReadyForNextOutgoingPacket = false;
            }
        }

        /// <summary>
        /// Notify the segment handler that an ACK has been received for the specified segment of the specified packet number.
        /// </summary>
        /// <param name="seqNum"></param>
        /// <param name="pcktNum"></param>
        public void AckReceived(uint seqNum, uint pcktNum)
        {
            // If we move onto the next packet, we are guaranteed to have received all ACKs for the previous packet.
            // So we can ignore any ACKs for the previous packet.
            //
            if (pcktNum != OutgoingPacketIndex)
            {
                logger.Warn($"Received ACK for packet {pcktNum}, expected {OutgoingPacketIndex}, ignoring");
                return;
            }

            if (!IncomingSegmentAcks.Contains(seqNum))
            {
                logger.Debug($"Received ACK for {seqNum}:{pcktNum}");
                IncomingSegmentAcks.Add(seqNum);
            }
            else
            {
                // TODO: should this actually ever occur?
                // Verify the logic, and if it should not occur, throw an exception.
                //
                logger.Warn($"Received duplicate ACK for {seqNum}:{pcktNum}, ignoring");
            }
        }

        public void NackReceived(uint seqNum, uint pcktNum, IPEndPoint endPoint)
        {
            if (pcktNum == OutgoingPacketIndex)
            {
                logger.Debug($"Received NACK for {seqNum}:{pcktNum}, resending");
                sendSegment(seqNum, pcktNum, endPoint);
            }
            else
            {
                // If we move onto the next packet, we are guaranteed to have received all ACKs for the previous packet.
                // So we can ignore any NACKs for the previous packet.
                //
                logger.Warn($"Received NACK for packet {pcktNum}, expected {OutgoingPacketIndex}, ignoring");
            }
        }

        /// <summary>
        /// Determines if all ACKs for the current packet have been received.
        /// </summary>
        /// <returns></returns>
        public bool AllAcksReceived()
        {
            return IncomingSegmentAcks.Count == NumberOfSegmentsToAck;
        }

        /// <summary>
        /// If all ACKs for the current packet have been received, this function sends the next packet in the queue.
        /// If there are no packets in the queue, the handler is marked as ready to send the next packet.
        /// </summary>
        /// <param name="endPoint"></param>
        public void SendNextPacketIfReady(IPEndPoint endPoint)
        {
            lock (PacketQueueMutex)
            {
                // If we have not received all ACKs for the current packet, we should not send the next packet.
                //
                if (!AllAcksReceived())
                {
                    return;
                }

                logger.Info($"All ACKs received for pckt num {OutgoingPacketIndex}, sending next packet");

                // Reset the outgoing packet state.
                //
                OutgoingPacketIndex++;
                NumberOfSegmentsToAck = 0;
                OutgoingSegments.Clear();
                IncomingSegmentAcks.Clear();

                // If there are packets in the queue, send the next packet.
                // Otherwise, mark the handler as ready to send the next packet.
                //
                if (OutgoingPacketQueue.Count > 0)
                {
                    sendPacket(OutgoingPacketQueue.Dequeue(), endPoint);
                }
                else
                {
                    ReadyForNextOutgoingPacket = true;
                }

            }
        }

        /// <summary>
        /// Adds a segment to the recombination queue.
        /// </summary>
        /// <param name="seqNum"></param>
        /// <param name="final"></param>
        /// <param name="data"></param>
        /// <returns>A list of sequence numbers to NACK for.</returns>
        public void SegmentReceived(uint seqNum, uint pcktNum, bool final, byte[] data, IPEndPoint endPoint)
        {
            //
            // TODO:
            // We send all NACKs when the final segment is received. This might be a problem, and we may
            // want to regularly send NACKs in the future.
            //

            if (pcktNum != IncomingPacketIndex)
            {
                logger.Warn($"Received packet num {pcktNum}, expected {IncomingPacketIndex}, resending ACK");

                // We moved on to the next packet, but the client resent the previous packet.
                // So it clearly missed the ACK for the previous packet. We need to resend the ACK.
                //
                SendAck(seqNum, pcktNum, endPoint);
                return;
            }

            // Acknowledge the packet.
            //
            SendAck(seqNum, pcktNum, endPoint);

            // Ignore duplicate packets.
            //
            if (IncomingSegments.ContainsKey(seqNum))
            {
                logger.Debug($"Received duplicate segment {seqNum}:{pcktNum}");
                return;
            }

            logger.Debug($"Received segment {seqNum}:{pcktNum}");

            IncomingSegments.Add(seqNum, data);

            // If this is the final segment, we need to check for missing segments.
            // If we are missing segments, we need to send NACKs for them.
            //
            if (final)
            {
                IncomingFinished = true;

                // Go through the list of sequence numbers and check if we have received them.
                //
                for (uint i = 0; i < seqNum; i++)
                {
                    if (!IncomingSegments.ContainsKey(i))
                    {
                        SendNack(i, pcktNum, endPoint);
                    }
                }
            }
        }

        /// <summary>
        /// Determines if all segments of a packet have been received.
        /// </summary>
        /// <returns></returns>
        public bool FullPacketReady()
        {
            if (!IncomingFinished)
            {
                return false;
            }

            for (int i = 1; i < IncomingSegments.Count; i++)
            {
                if (IncomingSegments.ElementAt(i).Key != IncomingSegments.ElementAt(i - 1).Key + 1)
                {
                    return false; // Found a gap, sequence is not complete
                }
            }

            return true; // No gaps found, sequence is complete
        }

        /// <summary>
        /// If a full packet is ready to be reassembled, this function returns the reassembled packet.
        /// Throws an InvalidOperationException if a full packet is not ready.
        /// </summary>
        /// <returns>The bytes of the packet.</returns>
        public byte[] ConsumeFullPacket()
        {
            if (!FullPacketReady())
            {
                throw new InvalidOperationException("Cannot consume full packet when it is not ready");
            }

            PacketBufferer bufferer = new PacketBufferer();

            for (uint i = 0; i < IncomingSegments.Count; i++)
            {
                bufferer.AddPacket(IncomingSegments[i]);
            }

            logger.Info($"Reassembled packet num {IncomingPacketIndex}");

            IncomingPacketIndex++;
            IncomingSegments.Clear();
            IncomingFinished = false;

            return bufferer.ConsumePacket();
        }

        /// <summary>
        /// Sends an ACK for the specified segment of the specified packet number.
        /// </summary>
        /// <param name="seqNum"></param>
        /// <param name="pcktNum"></param>
        /// <param name="remoteEndPoint"></param>
        public void SendAck(uint seqNum, uint pcktNum, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = conversationId,
                seqNum = seqNum,
                pcktNum = pcktNum,
                finish = 1,
                type = Shared.Txp.PacketType.ACK
            };

            logger.Info($"Sending ACK for {seqNum}:{pcktNum}");

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }

        /// <summary>
        /// Sends a NACK for the specified segment of the specified packet number.
        /// </summary>
        /// <param name="seqNum"></param>
        /// <param name="pcktNum"></param>
        /// <param name="remoteEndPoint"></param>
        public void SendNack(uint seqNum, uint pcktNum, IPEndPoint remoteEndPoint)
        {
            Shared.Txp.Header header = new Shared.Txp.Header
            {
                magic = Shared.Txp.Constants.MAGIC,
                checksum = 0,
                convId = conversationId,
                seqNum = seqNum,
                pcktNum = pcktNum,
                finish = 1,
                type = Shared.Txp.PacketType.NACK
            };

            logger.Info($"Sending NACK for {seqNum}:{pcktNum}");

            byte[] ackPacket = header.ToBytes();
            udpClient.Send(ackPacket, ackPacket.Length, remoteEndPoint);
        }
    }
}