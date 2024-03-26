using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared.Pip
{
    public static class Constants
    {
        public static uint MAGIC = 0x1337;
        public static ushort VERSION = 1;
        public static readonly Feature[] FEATURES = { Feature.SMTVerificationFeature };
    }
}
