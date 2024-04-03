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
        // Helper method to convert a byte array to a structure with big endian handling
        public static T ByteArrayToStructure<T>(byte[] data) where T : struct
        {
            byte[] copy = new byte[data.Length];
            Array.Copy(data, copy, data.Length);

            ReverseBytesForBigEndian(copy, typeof(T));

            var handle = GCHandle.Alloc(copy, GCHandleType.Pinned);
            try
            {
                return (T)Marshal.PtrToStructure(handle.AddrOfPinnedObject(), typeof(T));
            }
            finally
            {
                handle.Free();
            }
        }

        // Helper method to convert a structure to a byte array with big endian handling
        public static byte[] StructureToByteArray<T>(T structure) where T : struct
        {
            int size = Marshal.SizeOf(structure);
            byte[] byteArray = new byte[size];
            IntPtr ptr = Marshal.AllocHGlobal(size);

            try
            {
                Marshal.StructureToPtr(structure, ptr, true);
                Marshal.Copy(ptr, byteArray, 0, size);
                ReverseBytesForBigEndian(byteArray, typeof(T));
            }
            finally
            {
                Marshal.FreeHGlobal(ptr);
            }

            return byteArray;
        }

        // Method to reverse bytes of fields for big endian compatibility
        private static void ReverseBytesForBigEndian(byte[] data, Type type)
        {
            if (!BitConverter.IsLittleEndian)
            {
                return;
            }

            foreach (var field in type.GetFields())
            {
                if (field.FieldType.IsPrimitive)
                {
                    var fieldType = field.FieldType;
                    int sizeOfField = Marshal.SizeOf(fieldType);
                    int offset = Marshal.OffsetOf(type, field.Name).ToInt32();

                    // Reverse bytes only for integral types (excluding chars)
                    if (fieldType == typeof(int) || fieldType == typeof(uint) ||
                        fieldType == typeof(short) || fieldType == typeof(ushort) ||
                        fieldType == typeof(long) || fieldType == typeof(ulong) ||
                        fieldType == typeof(float) || fieldType == typeof(double))
                    {
                        Array.Reverse(data, offset, sizeOfField);
                    }
                }
            }
        }

        public static byte[] GetBytes(uint value)
        {
            byte[] bytes = BitConverter.GetBytes(value);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            return bytes;
        }
        public static byte[] GetBytes(int value)
        {
            byte[] bytes = BitConverter.GetBytes(value);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            return bytes;
        }
        public static byte[] GetBytes(ushort value)
        {
            byte[] bytes = BitConverter.GetBytes(value);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            return bytes;
        }

        public static uint ToUInt32(byte[] bytes, int index = 0)
        {
            byte[] copy = new byte[sizeof(uint)];
            Array.Copy(bytes, index, copy, 0, sizeof(uint));

            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(copy);
            }

            return BitConverter.ToUInt32(copy);
        }
        public static int ToInt32(byte[] bytes, int index = 0)
        {
            byte[] copy = new byte[sizeof(int)];
            Array.Copy(bytes, index, copy, 0, sizeof(int));

            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(copy);
            }

            return BitConverter.ToInt32(copy);
        }

        public static ushort ToUInt16(byte[] bytes, int index = 0)
        {
            byte[] copy = new byte[sizeof(ushort)];
            Array.Copy(bytes, index, copy, 0, sizeof(ushort));

            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(copy);
            }

            return BitConverter.ToUInt16(copy);
        }
    }
}
