using Microsoft.Z3;

var unSatExample = "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (= (- x y) (+ x (- y) 1))) (check-sat)";
var satExample = "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (= (+ x (* 2 y)) 20)) (assert (= (- x y) 2)) (check-sat)";

void checkModel(string modelStr)
{
    using (Context z3Ctx = new Context())
    {
        var model = z3Ctx.ParseSMTLIB2String(modelStr);

        var solver = z3Ctx.MkSimpleSolver();

        solver.Assert(model);

        if (solver.Check() == Status.SATISFIABLE)
        {
            Console.WriteLine($"{modelStr} -> SAT");
        }
        else
        {
            Console.WriteLine($"{modelStr} -> UNSAT");
        }
    }
}

checkModel(unSatExample);
checkModel(satExample);