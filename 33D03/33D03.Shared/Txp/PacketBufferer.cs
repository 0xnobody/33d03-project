using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public class PacketBufferer
    {
        private byte[] buffer;

        public PacketBufferer()
        {
            buffer = new byte[0];
        }

        public void AddPacket(byte[] packet)
        {
            Array.Resize(ref buffer, buffer.Length + packet.Length);
            packet.CopyTo(buffer, buffer.Length - packet.Length);
        }

        public byte[] ConsumePacket()
        {
            byte[] cp = buffer;
            buffer = new byte[0];
            return cp;
        }
    }
}
