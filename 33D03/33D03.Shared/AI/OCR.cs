using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Tesseract;

namespace _33D03.Shared.AI
{
    public static class OCR
    {
        public static Tuple<string, float>? Classify(byte[] imageData)
        {
            try
            {
                using (var engine = new TesseractEngine(@"./tessdata", "eng", EngineMode.Default))
                {
                    using (var img = Pix.LoadFromMemory(imageData))
                    {
                            var i = 1;
                            using (var page = engine.Process(img))
                            {
                                return new Tuple<string, float>(page.GetText(), page.GetMeanConfidence());
                            }
                        }
                }
            }
            catch (Exception e)
            {
                Trace.TraceError(e.ToString());
                Console.WriteLine("Unexpected Error: " + e.Message);
                Console.WriteLine("Details: ");
                Console.WriteLine(e.ToString());
            }

            return null;
        }
    }
}
