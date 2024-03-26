using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Z3;

namespace _33D03.Shared.Z3
{
    public static class Z3Helper
    {
        public static Status CheckModel(string modelStr)
        {
            using (Context z3Ctx = new Context())
            {
                var model = z3Ctx.ParseSMTLIB2String(modelStr);

                var solver = z3Ctx.MkSimpleSolver();

                solver.Assert(model);

                return solver.Check();
            }
        }
    }
}
