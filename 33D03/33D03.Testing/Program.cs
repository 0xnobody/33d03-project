using Microsoft.Z3;
using _33D03.Shared.AI;
using Keras;

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

void detectText(string imagePath)
{    
    var bytes = File.ReadAllBytes(imagePath);

    (var text, var confidence) = OCR.Classify(bytes);

    Console.WriteLine($"Text: {text} with confidence {confidence}");
}

detectText(@"C:\Users\adamn\Downloads\sample.png");

//checkModel(unSatExample);
//checkModel(satExample);
