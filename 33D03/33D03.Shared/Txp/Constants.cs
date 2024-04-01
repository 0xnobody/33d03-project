using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Txp
{
    public static class Constants
    {
        public const int PACKET_SIZE = 256;
        public const int HEADER_SIZE = 24;
        public const int DATA_SIZE = PACKET_SIZE - HEADER_SIZE;
        public const int MAGIC = 0x33D03;
        public const int ACK_TIMEOUT_MS = 500;
        public const int SYN_TIMEOUT_MS = 5000;
        public const int SYN_MAX_ATTEMPTS = 3;
    }

}
