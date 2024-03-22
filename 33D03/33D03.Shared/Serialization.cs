using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Shared
{
    internal static class Serialization
    {
        // Generic method to convert a byte array to a struct
        public static T ByteArrayToStructure<T>(byte[] data) where T : struct
        {
            var handle = GCHandle.Alloc(data, GCHandleType.Pinned);
            try
            {
                return (T)Marshal.PtrToStructure(handle.AddrOfPinnedObject(), typeof(T));
            }
            finally
            {
                handle.Free();
            }
        }

        // Helper method to convert a structure to a byte array
        public static byte[] StructureToByteArray<T>(T structure) where T : struct
        {
            int size = Marshal.SizeOf(structure);
            byte[] byteArray = new byte[size];
            IntPtr ptr = Marshal.AllocHGlobal(size);
            Marshal.StructureToPtr(structure, ptr, true);
            Marshal.Copy(ptr, byteArray, 0, size);
            Marshal.FreeHGlobal(ptr);
            return byteArray;
        }
    }
}
