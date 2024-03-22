using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared
{
    public static class Checksum
    {
        public static uint Calculate(byte[] data)
        {
            // CRC32 Algorithm
            const uint polynomial = 0xedb88320;
            uint[] table = new uint[256];
            uint crc = 0xffffffff;
            for (uint i = 0; i < 256; i++)
            {
                uint c = i;
                for (int j = 8; j > 0; j--)
                {
                    if ((c & 1) == 1)
                    {
                        c = (c >> 1) ^ polynomial;
                    }
                    else
                    {
                        c >>= 1;
                    }
                }
                table[i] = c;
            }
            for (uint i = 0; i < data.Length; i++)
            {
                crc = (crc >> 8) ^ table[(crc & 0xff) ^ data[i]];
            }
            return ~crc;
        }
    }
}
