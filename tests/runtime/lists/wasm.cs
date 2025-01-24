using System;
using System.Runtime.InteropServices;
using System.Diagnostics;
using ListsWorld.wit.imports.test.lists;
using System.Text;

namespace ListsWorld {

    public class ListsWorldImpl : IListsWorld
    {
        public static uint AllocatedBytes()
        {
            return 0;
        }

        public static void TestImports()
        {

            TestInterop.EmptyListParam(new byte[0]);
            TestInterop.EmptyStringParam("");

            {
                byte[] result = TestInterop.EmptyListResult();
                Debug.Assert(result.Length == 0);
            }

            {
                string result = TestInterop.EmptyStringResult();
                Debug.Assert(result.Length == 0);
            }

            TestInterop.ListParam(new byte[] { (byte)1, (byte)2, (byte)3, (byte)4 });
            TestInterop.ListParam((new byte[] { (byte)1, (byte)2, (byte)3, (byte)4 }).AsSpan());
            TestInterop.ListParam((new byte[] { (byte)1, (byte)2, (byte)3, (byte)4 }).AsMemory());
            TestInterop.ListParam2("foo");
            TestInterop.ListParam3(new List<String>() {
                "foo",
                "bar",
                "baz"
            });

            TestInterop.ListParam4(new List<List<String>>() {
                new List<String>() {
                    "foo",
                    "bar"
               },
                new List<String>() {
                    "baz"
                }
            });

            {
               byte[] result = TestInterop.ListResult();
               Debug.Assert(result.Length == 5);
               Debug.Assert(result[0] == (byte)1);
               Debug.Assert(result[1] == (byte)2);
               Debug.Assert(result[2] == (byte)3);
               Debug.Assert(result[3] == (byte)4);
               Debug.Assert(result[4] == (byte)5);
            }

            {
               string result = TestInterop.ListResult2();
               Console.WriteLine(result);
               Debug.Assert(result == "hello!");
            }

            {
               List<String> result = TestInterop.ListResult3();
               Debug.Assert(result.Count() == 2);
               Console.WriteLine(result[0]);
               Console.WriteLine(result[1]);
               Debug.Assert(result[0] == "hello,");
               Debug.Assert(result[1] == "world!");
            }

            string[] strings = { "x", "", "hello", "hello ⚑ world" };
            foreach (string s in strings)
            {
                string result = TestInterop.StringRoundtrip(s);
                Debug.Assert(result == s);

                byte[] bytes = Encoding.UTF8.GetBytes(s);
                Debug.Assert(bytes.SequenceEqual(TestInterop.ListRoundtrip(bytes)));
            }

            {
                var (u, s) = TestInterop.ListMinmax8(
                    new byte[] { byte.MinValue,byte.MaxValue },
                    new sbyte[] { sbyte.MinValue, sbyte.MaxValue }
                );

                Debug.Assert(u.Length == 2 && u[0] == byte.MinValue && u[1] == byte.MaxValue);
                Debug.Assert(s.Length == 2 && s[0] == sbyte.MinValue && s[1] == sbyte.MaxValue);
            }

            {
                var (u, s) = TestInterop.ListMinmax16(
                    new ushort[] { ushort.MinValue, ushort.MaxValue },
                    new short[] { short.MinValue, short.MaxValue }
                );

                Console.WriteLine(u[0]);
                Console.WriteLine(u[1]);
                Debug.Assert(u.Length == 2, $"u.Length {u.Length}");
                Debug.Assert(u[0] == ushort.MinValue, $"u[0] == {u[0]}");
                Debug.Assert(u[1] == ushort.MaxValue, $"u[1] == {u[1]}");

                Debug.Assert(s.Length == 2);
                Console.WriteLine(s[0]);
                Console.WriteLine(s[1]);
                Debug.Assert(s.Length == 2 && s[0] == short.MinValue && s[1] == short.MaxValue);
            }

            {
                var (u, s) = TestInterop.ListMinmax32(
                    new uint[] { uint.MinValue, uint.MaxValue },
                    new int[] { int.MinValue, int.MaxValue }
                );

                Debug.Assert(u.Length == 2 && u[0] == uint.MinValue && u[1] == uint.MaxValue);
                Debug.Assert(s.Length == 2 && s[0] == int.MinValue && s[1] == int.MaxValue);
            }

            {
                var (u, s) = TestInterop.ListMinmax64(
                    new ulong[] { ulong.MinValue, ulong.MaxValue },
                    new long[] { long.MinValue, long.MaxValue }
                );

                Debug.Assert(u.Length == 2 && u[0] == ulong.MinValue && u[1] == ulong.MaxValue);

                Debug.Assert(s.Length == 2 && s[0] == long.MinValue && s[1] == long.MaxValue);
            }

            {
                var (u, s) = TestInterop.ListMinmaxFloat(
                    new float[] {
                        float.MinValue,
                        float.MaxValue,
                        float.NegativeInfinity,
                        float.PositiveInfinity
                    },
                    new double[] {
                        double.MinValue,
                        double.MaxValue,
                        double.NegativeInfinity,
                        double.PositiveInfinity
                    });

                Debug.Assert(u.Length == 4
                    && u[0] == float.MinValue
                    && u[1] == float.MaxValue
                    && u[2] == float.NegativeInfinity
                    && u[3] == float.PositiveInfinity);

                Debug.Assert(s.Length == 4
                    && s[0] == double.MinValue
                    && s[1] == double.MaxValue
                    && s[2] == double.NegativeInfinity
                    && s[3] == double.PositiveInfinity);
            }
        }
    }
}

namespace ListsWorld.wit.exports.test.lists
{
    public class TestImpl : ITest
    {

        public static void EmptyListParam(byte[] a)
        {
            Debug.Assert(a.Length == 0);
        }

        public static void EmptyStringParam(string a)
        {
            Debug.Assert(a.Length == 0);
        }

        public static byte[] EmptyListResult()
        {
            return new byte[0];
        }

        public static string EmptyStringResult()
        {
            return "";
        }

        public static void ListParam(byte[] a)
        {
            Debug.Assert(a.Length == 4);
            Debug.Assert(a[0] == 1);
            Debug.Assert(a[1] == 2);
            Debug.Assert(a[2] == 3);
            Debug.Assert(a[3] == 4);
        }

        public static void ListParam2(string a)
        {
            Debug.Assert(a.Equals("foo"));
        }

        public static void ListParam3(List<String> a)
        {
            Debug.Assert(a.Count() == 3);
            Debug.Assert(a[0].Equals("foo"));
            Debug.Assert(a[1].Equals("bar"));
            Debug.Assert(a[2].Equals("baz"));
        }

        public static void ListParam4(List<List<String>> a)
        {
            Debug.Assert(a.Count() == 2);
            Debug.Assert(a[0].Count() == 2);
            Debug.Assert(a[1].Count() == 1);

            Debug.Assert(a[0][0].Equals("foo"));
            Debug.Assert(a[0][1].Equals("bar"));
            Debug.Assert(a[1][0].Equals("baz"));
        }

        public static void ListParam5(List<(byte, uint, byte)> a)
        {
            Debug.Assert(a.Count() == 2);
            Debug.Assert(a[0].Item1 == 1);
            Debug.Assert(a[0].Item2 == 2);
            Debug.Assert(a[0].Item3 == 3);
            Debug.Assert(a[1].Item1 == 4);
            Debug.Assert(a[1].Item2 == 5);
            Debug.Assert(a[1].Item3 == 6);
        }

        public static byte[] ListResult()
        {
            return new byte[] { (byte)1, (byte)2, (byte)3, (byte)4, (byte)5 };
        }

        public static string ListResult2()
        {
            return "hello!";
        }

        public static List<string> ListResult3()
        {
            return new List<string>() {
                "hello,",
                "world!"
                };
        }

        public static byte[] ListRoundtrip(byte[] a)
        {
            return a;
        }

        public static string stringRoundtrip(string a)
        {
            return a;
        }

        public static (byte[], byte[]) ListMinmax8(byte[] a, byte[] b)
        {
            return new(a, b);
        }

        public static (short[], short[]) ListMinmax16(short[] a, short[] b)
        {
            return new(a, b);
        }

        public static (int[], int[]) ListMinmax32(int[] a, int[] b)
        {
            return new(a, b);
        }

        public static (long[], long[]) ListMinmax64(long[] a, long[] b)
        {
            return new(a, b);
        }

        public static (float[], double[]) ListMinmaxFloat(float[] a, double[] b)
        {
            return new(a, b);
        }
        public static (byte[], sbyte[]) ListMinmax8(byte[] a, sbyte[] b)
        {
            return (a, b);
        }

        public static (ushort[], short[]) ListMinmax16(ushort[] a, short[] b)
        {
            return (a, b);
        }

        public static (uint[], int[]) ListMinmax32(uint[] a, int[] b)
        {
            return (a, b);
        }

        public static (ulong[], long[]) ListMinmax64(ulong[] a, long[] b)
        {
            return (a, b);
        }

        public static string StringRoundtrip(string a)
        {
            return a;
        }
    }
}
