import { readFileSync } from 'fs';
import * as assert from 'assert';
import * as imports from './imports/bindings.js';
import * as exports from './exports/bindings.js';
import { WASI } from 'wasi';

async function run() {
  const wasm = readFileSync(process.argv[2]);
  const wasi = new WASI({
    args: process.argv,
    env: process.env,
  });
  const importObj = {
    wasi_snapshot_preview1: wasi.wasiImport,
  };
  let instance: WebAssembly.Instance | null = null;
  imports.addHostToImports(importObj, host(), name => {
    if (instance === null)
      throw new Error("instance not ready yet");
    return instance.exports[name];
  });
  const wasmObj = new exports.Wasm();
  await wasmObj.instantiate(wasm, importObj);
  instance = wasmObj.instance;
  wasi.initialize(instance);

  runTests(wasmObj);

  // test other methods of creating a wasm wrapper
  (new exports.Wasm()).instantiate(wasm.buffer, importObj);
  (new exports.Wasm()).instantiate(new Uint8Array(wasm), importObj);
  (new exports.Wasm()).instantiate(new WebAssembly.Module(wasm), importObj);
  {
    const obj = new exports.Wasm();
    obj.addToImports(importObj);
    obj.instantiate(new WebAssembly.Instance(new WebAssembly.Module(wasm), importObj));
  }
}

function host(): imports.Host {
  let scalar = 0;
  let sawClose = false;
  return {
    roundtripU8(x) { return x; },
    roundtripS8(x) { return x; },
    roundtripU16(x) { return x; },
    roundtripS16(x) { return x; },
    roundtripU32(x) { return x; },
    roundtripS32(x) { return x; },
    roundtripU64(x) { return x; },
    roundtripS64(x) { return x; },
    roundtripF32(x) { return x; },
    roundtripF64(x) { return x; },
    roundtripChar(x) { return x; },
    multipleResults() { return [4, 5]; },
    setScalar(x) { scalar = x; },
    getScalar() { return scalar; },
    swapTuple([a, b]) { return [b, a]; },
    roundtripFlags1(x) { return x; },
    roundtripFlags2(x) { return x; },
    roundtripFlags3(r0, r1, r2, r3) { return [r0, r1, r2, r3]; },
    roundtripRecord1(x) { return x; },
    tuple0([]) { return []; },
    tuple1([x]) { return [x]; },
    roundtripOption(x) { return x; },
    roundtripResult(x) {
      if (x.tag == 'ok') {
        return { tag: 'ok', val: x.val };
      } else {
        return { tag: 'err', val: Math.round(x.val) };
      }
    },
    roundtripEnum(x) { return x; },
    invertBool(x) { return !x; },
    variantCasts(x) { return x; },
    variantZeros(x) { return x; },
    variantTypedefs(x, y, z) {},
    variantEnums(a, b, c) {
      assert.deepStrictEqual(a, true);
      assert.deepStrictEqual(b, { tag: 'ok' });
      assert.deepStrictEqual(c, imports.MyErrno.Success);
      return [
        false,
        { tag: 'err', val: undefined },
        imports.MyErrno.A,
      ];
    },
    listParam(a) {
      assert.deepStrictEqual(Array.from(a), [1, 2, 3, 4]);
    },
    listParam2(a) {
      assert.strictEqual(a, 'foo');
    },
    listParam3(a) {
      assert.deepStrictEqual(a, ['foo', 'bar', 'baz']);
    },
    listParam4(a) {
      assert.deepStrictEqual(a, [['foo', 'bar'], ['baz']]);
    },
    listResult() {
      return new Uint8Array([1, 2, 3, 4, 5]);
    },
    listResult2() { return 'hello!'; },
    listResult3() { return ['hello,', 'world!']; },
    stringRoundtrip(x) { return x; },
    hostStateCreate() { return 100; },
    hostStateGet(x) { return x as number; },
    hostState2Create() { return 101; },
    hostState2SawClose() { return sawClose; },
    dropHostState2(state) { sawClose = true; },
    twoHostStates(a, b) { return [b, a]; },
    hostState2ParamRecord(x) {},
    hostState2ParamTuple(x) {},
    hostState2ParamOption(x) {},
    hostState2ParamResult(x) {},
    hostState2ParamVariant(x) {},
    hostState2ParamList(x) {},

    hostState2ResultRecord() { return { a: {} }; },
    hostState2ResultTuple() { return [{}]; },
    hostState2ResultOption() { return 102; },
    hostState2ResultResult() { return { tag: 'ok', val: {} }; },
    hostState2ResultVariant() { return { tag: '0', val: {} }; },
    hostState2ResultList() { return [{}, 3]; },

    bufferU8(x, out) {
      assert.deepStrictEqual(Array.from(x), [0]);
      assert.deepStrictEqual(out.length, 10);
      out[0] = 1;
      out[1] = 2;
      out[2] = 3;
      return 3;
    },
    bufferU32(x, out) {
      assert.deepStrictEqual(Array.from(x), [0]);
      assert.deepStrictEqual(out.length, 10);
      out[0] = 1;
      out[1] = 2;
      out[2] = 3;
      return 3;
    },
    bufferBool(x, out) {
      assert.ok(x.length <= out.length);
      let amt = 0;
      while (true) {
        const val = x.pull();
        if (val === undefined)
          break;
        out.push(!val);
        amt += 1;
      }
      return amt;
    },
    bufferMutable1(x) {
      assert.strictEqual(x.length, 1);
      assert.strictEqual(x[0].length, 5);
      assert.strictEqual(x[0].pull(), true);
      assert.strictEqual(x[0].pull(), false);
      assert.strictEqual(x[0].pull(), true);
      assert.strictEqual(x[0].pull(), true);
      assert.strictEqual(x[0].pull(), false);
      assert.strictEqual(x[0].pull(), undefined);
    },
    bufferMutable2(x) {
      assert.strictEqual(x.length, 1);
      assert.ok(x[0].length > 4);
      x[0].set([1, 2, 3, 4]);
      return 4;
    },
    bufferMutable3(x) {
      assert.strictEqual(x.length, 1);
      assert.ok(x[0].length > 3);
      x[0].push(false);
      x[0].push(true);
      x[0].push(false);
      return 3;
    },
    bufferInRecord(x) { },
    bufferTypedef(a, b, c, d) {},

    listInRecord1(x) {},
    listInRecord2() { return { a: 'list_in_record2' }; },
    listInRecord3(x) {
      assert.strictEqual(x.a, 'list_in_record3 input');
      return { a: 'list_in_record3 output' };
    },
    listInRecord4(x) {
      assert.strictEqual(x.a, 'input4');
      return { a: 'result4' };
    },
    listInVariant1(a, b, c) {
      assert.strictEqual(a, 'foo');
      assert.deepStrictEqual(b, { tag: 'err', val: 'bar' });
      assert.deepStrictEqual(c, { tag: '0', val: 'baz' });
    },
    listInVariant2() { return 'list_in_variant2'; },
    listInVariant3(x) {
      assert.strictEqual(x, 'input3');
      return 'output3';
    },

    errnoResult() { return { tag: 'err', val: imports.MyErrno.B }; },
    listTypedefs(x, y) {
      assert.strictEqual(x, 'typedef1');
      assert.deepStrictEqual(y, ['typedef2']);
      return [(new TextEncoder).encode('typedef3'), ['typedef4']];
    },

    listOfVariants(bools, results, enums) {
      assert.deepStrictEqual(bools, [true, false]);
      assert.deepStrictEqual(results, [{ tag: 'ok' }, { tag: 'err' }]);
      assert.deepStrictEqual(enums, [imports.MyErrno.Success, imports.MyErrno.A]);
      return [
        [false, true],
        [{ tag: 'err', val: undefined }, { tag: 'ok', val: undefined }],
        [imports.MyErrno.A, imports.MyErrno.B],
      ];
    },

    unalignedRoundtrip1(u16, u32, u64, flag32, flag64) {
      assert.deepStrictEqual(Array.from(u16), [1]);
      assert.deepStrictEqual(Array.from(u32), [2]);
      assert.deepStrictEqual(Array.from(u64), [3n]);
      assert.deepStrictEqual(flag32, [imports.FLAG32_B8]);
      assert.deepStrictEqual(flag64, [imports.FLAG64_B9]);
    },
    unalignedRoundtrip2(record, f32, f64, string, list) {
      assert.deepStrictEqual(Array.from(record), [{ a: 10, b: 11n }]);
      assert.deepStrictEqual(Array.from(f32), [100]);
      assert.deepStrictEqual(Array.from(f64), [101]);
      assert.deepStrictEqual(string, ['foo']);
      assert.deepStrictEqual(list, [new Uint8Array([102])]);
    },

    markdown2Create() {
      class Markdown {
        buf: string;

        constructor() {
          this.buf = '';
        }
        append(extra) {
          this.buf += extra;
        }
        render() {
          return this.buf.replace('red', 'green');
        }
      }

      return new Markdown();
    },

    listMinmax8(u, s) {
      assert.deepEqual(u.length, 2);
      assert.deepEqual(u[0], 0);
      assert.deepEqual(u[1], (1 << 8) - 1);
      assert.deepEqual(s.length, 2);
      assert.deepEqual(s[0], -(1 << 7));
      assert.deepEqual(s[1], (1 << 7) - 1);

      return [u, s];
    },

    listMinmax16(u, s) {
      assert.deepEqual(u.length, 2);
      assert.deepEqual(u[0], 0);
      assert.deepEqual(u[1], (1 << 16) - 1);
      assert.deepEqual(s.length, 2);
      assert.deepEqual(s[0], -(1 << 15));
      assert.deepEqual(s[1], (1 << 15) - 1);

      return [u, s];
    },

    listMinmax32(u, s) {
      assert.deepEqual(u.length, 2);
      assert.deepEqual(u[0], 0);
      assert.deepEqual(u[1], ~0 >>> 0);
      assert.deepEqual(s.length, 2);
      assert.deepEqual(s[0], 1 << 31);
      assert.deepEqual(s[1], ((1 << 31) - 1) >>> 0);

      return [u, s];
    },

    listMinmax64(u, s) {
      assert.deepEqual(u.length, 2);
      assert.deepEqual(u[0], 0n);
      assert.deepEqual(u[1], (2n ** 64n) - 1n);
      assert.deepEqual(s.length, 2);
      assert.deepEqual(s[0], -(2n ** 63n));
      assert.deepEqual(s[1], (2n ** 63n) - 1n);

      return [u, s];
    },

    listMinmaxFloat(f, d) {
      assert.deepEqual(f.length, 4);
      assert.deepEqual(f[0], -3.4028234663852886e+38);
      assert.deepEqual(f[1], 3.4028234663852886e+38);
      assert.deepEqual(f[2], Number.NEGATIVE_INFINITY);
      assert.deepEqual(f[3], Number.POSITIVE_INFINITY);

      assert.deepEqual(d.length, 4);
      assert.deepEqual(d[0], -Number.MAX_VALUE);
      assert.deepEqual(d[1], Number.MAX_VALUE);
      assert.deepEqual(d[2], Number.NEGATIVE_INFINITY);
      assert.deepEqual(d[3], Number.POSITIVE_INFINITY);

      return [f, d];
    },
  };
}

function runTests(wasm: exports.Wasm) {
  const bytes = wasm.allocatedBytes();
  wasm.runImportTests();
  testScalars(wasm);
  testRecords(wasm);
  testVariants(wasm);
  testLists(wasm);
  testFlavorful(wasm);
  testInvalid(wasm);
  testHandles(wasm);
  // buffers(wasm);

  // Ensure that we properly called `free` everywhere in all the glue that we
  // needed to.
  assert.strictEqual(bytes, wasm.allocatedBytes());
}

function testScalars(wasm: exports.Wasm) {
  assert.strictEqual(wasm.roundtripU8(1), 1);
  assert.strictEqual(wasm.roundtripU8((1 << 8) - 1), (1 << 8) - 1);

  assert.strictEqual(wasm.roundtripS8(1), 1);
  assert.strictEqual(wasm.roundtripS8((1 << 7) - 1), (1 << 7) - 1);
  assert.strictEqual(wasm.roundtripS8(-(1 << 7)), -(1 << 7));

  assert.strictEqual(wasm.roundtripU16(1), 1);
  assert.strictEqual(wasm.roundtripU16((1 << 16) - 1), (1 << 16) - 1);

  assert.strictEqual(wasm.roundtripS16(1), 1);
  assert.strictEqual(wasm.roundtripS16((1 << 15) - 1), (1 << 15) - 1);
  assert.strictEqual(wasm.roundtripS16(-(1 << 15)), -(1 << 15));

  assert.strictEqual(wasm.roundtripU32(1), 1);
  assert.strictEqual(wasm.roundtripU32(~0 >>> 0), ~0 >>> 0);

  assert.strictEqual(wasm.roundtripS32(1), 1);
  assert.strictEqual(wasm.roundtripS32(((1 << 31) - 1) >>> 0), ((1 << 31) - 1) >>> 0);
  assert.strictEqual(wasm.roundtripS32(1 << 31), 1 << 31);

  assert.strictEqual(wasm.roundtripU64(1n), 1n);
  assert.strictEqual(wasm.roundtripU64((1n << 64n) - 1n), (1n << 64n) - 1n);

  assert.strictEqual(wasm.roundtripS64(1n), 1n);
  assert.strictEqual(wasm.roundtripS64((1n << 63n) - 1n), (1n << 63n) - 1n);
  assert.strictEqual(wasm.roundtripS64(-(1n << 63n)), -(1n << 63n));

  assert.deepEqual(wasm.multipleResults(), [100, 200]);

  assert.strictEqual(wasm.roundtripF32(1), 1);
  assert.strictEqual(wasm.roundtripF32(Infinity), Infinity);
  assert.strictEqual(wasm.roundtripF32(-Infinity), -Infinity);
  assert.ok(Number.isNaN(wasm.roundtripF32(NaN)));

  assert.strictEqual(wasm.roundtripF64(1), 1);
  assert.strictEqual(wasm.roundtripF64(Infinity), Infinity);
  assert.strictEqual(wasm.roundtripF64(-Infinity), -Infinity);
  assert.ok(Number.isNaN(wasm.roundtripF64(NaN)));

  assert.strictEqual(wasm.roundtripChar('a'), 'a');
  assert.strictEqual(wasm.roundtripChar(' '), ' ');
  assert.strictEqual(wasm.roundtripChar('🚩'), '🚩');

  wasm.setScalar(2);
  assert.strictEqual(wasm.getScalar(), 2);
  wasm.setScalar(4);
  assert.strictEqual(wasm.getScalar(), 4);
}

function testRecords(wasm: exports.Wasm) {
  assert.deepStrictEqual(wasm.swapTuple([1, 2]), [2, 1]);
  assert.deepEqual(wasm.roundtripFlags1(exports.F1_A), exports.F1_A);
  assert.deepEqual(wasm.roundtripFlags1(0), 0);
  assert.deepEqual(wasm.roundtripFlags1(exports.F1_A | exports.F1_B), exports.F1_A | exports.F1_B);

  assert.deepEqual(wasm.roundtripFlags2(exports.F2_C), exports.F2_C);
  assert.deepEqual(wasm.roundtripFlags2(0), 0);
  assert.deepEqual(wasm.roundtripFlags2(exports.F2_D), exports.F2_D);
  assert.deepEqual(wasm.roundtripFlags2(exports.F2_C | exports.F2_E), exports.F2_C | exports.F2_E);

  {
    const { a, b } = wasm.roundtripRecord1({ a: 8, b: 0 });
    assert.deepEqual(a, 8);
    assert.deepEqual(b, 0);
  }

  {
    const { a, b } = wasm.roundtripRecord1({ a: 0, b: exports.F1_A | exports.F1_B });
    assert.deepEqual(a, 0);
    assert.deepEqual(b, exports.F1_A | exports.F1_B);
  }

  assert.deepStrictEqual(wasm.tuple0([]), []);
  assert.deepStrictEqual(wasm.tuple1([1]), [1]);
}

function testVariants(wasm: exports.Wasm) {
  assert.deepStrictEqual(wasm.roundtripOption(1), 1);
  assert.deepStrictEqual(wasm.roundtripOption(null), null);
  assert.deepStrictEqual(wasm.roundtripOption(2), 2);
  assert.deepStrictEqual(wasm.roundtripResult({ tag: 'ok', val: 2 }), { tag: 'ok', val: 2 });
  assert.deepStrictEqual(wasm.roundtripResult({ tag: 'ok', val: 4 }), { tag: 'ok', val: 4 });
  const f = Math.fround(5.2);
  assert.deepStrictEqual(wasm.roundtripResult({ tag: 'err', val: f }), { tag: 'err', val: 5 });

  assert.deepStrictEqual(wasm.roundtripEnum(exports.E1.A), exports.E1.A);
  assert.deepStrictEqual(wasm.roundtripEnum(exports.E1.B), exports.E1.B);

  assert.deepStrictEqual(wasm.invertBool(true), false);
  assert.deepStrictEqual(wasm.invertBool(false), true);

  {
    const a: exports.E1.A = exports.E1.A;
    const b: exports.E1.B = exports.E1.B;
  }

  {
    const [a1, a2, a3, a4, a5, a6] = wasm.variantCasts([
      { tag: 'a', val: 1 },
      { tag: 'a', val: 2 },
      { tag: 'a', val: 3 },
      { tag: 'a', val: 4n },
      { tag: 'a', val: 5n },
      { tag: 'a', val: 6 },
    ]);
    assert.deepStrictEqual(a1, { tag: 'a', val: 1 });
    assert.deepStrictEqual(a2, { tag: 'a', val: 2 });
    assert.deepStrictEqual(a3, { tag: 'a', val: 3 });
    assert.deepStrictEqual(a4, { tag: 'a', val: 4n });
    assert.deepStrictEqual(a5, { tag: 'a', val: 5n });
    assert.deepStrictEqual(a6, { tag: 'a', val: 6 });
  }
  {
    const [b1, b2, b3, b4, b5, b6] = wasm.variantCasts([
      { tag: 'b', val: 1n },
      { tag: 'b', val: 2 },
      { tag: 'b', val: 3 },
      { tag: 'b', val: 4 },
      { tag: 'b', val: 5 },
      { tag: 'b', val: 6 },
    ]);
    assert.deepStrictEqual(b1, { tag: 'b', val: 1n });
    assert.deepStrictEqual(b2, { tag: 'b', val: 2 });
    assert.deepStrictEqual(b3, { tag: 'b', val: 3 });
    assert.deepStrictEqual(b4, { tag: 'b', val: 4 });
    assert.deepStrictEqual(b5, { tag: 'b', val: 5 });
    assert.deepStrictEqual(b6, { tag: 'b', val: 6 });
  }

  {
    const [a1, a2, a3, a4] = wasm.variantZeros([
      { tag: 'a', val: 1 },
      { tag: 'a', val: 2n },
      { tag: 'a', val: 3 },
      { tag: 'a', val: 4 },
    ]);
    assert.deepStrictEqual(a1, { tag: 'a', val: 1 });
    assert.deepStrictEqual(a2, { tag: 'a', val: 2n });
    assert.deepStrictEqual(a3, { tag: 'a', val: 3 });
    assert.deepStrictEqual(a4, { tag: 'a', val: 4 });
  }

  wasm.variantTypedefs(null, false, { tag: 'err' });
}

function testLists(wasm: exports.Wasm) {
    wasm.listParam(new Uint8Array([1, 2, 3, 4]));
    wasm.listParam2("foo");
    wasm.listParam3(["foo", "bar", "baz"]);
    wasm.listParam4([["foo", "bar"], ["baz"]]);
    assert.deepStrictEqual(Array.from(wasm.listResult()), [1, 2, 3, 4, 5]);
    assert.deepStrictEqual(wasm.listResult2(), "hello!");
    assert.deepStrictEqual(wasm.listResult3(), ["hello,", "world!"]);

    assert.deepStrictEqual(wasm.stringRoundtrip("x"), "x");
    assert.deepStrictEqual(wasm.stringRoundtrip(""), "");
    assert.deepStrictEqual(wasm.stringRoundtrip("hello ⚑ world"), "hello ⚑ world");
}

function testFlavorful(wasm: exports.Wasm) {
  wasm.listInRecord1({ a: "list_in_record1" });
  assert.deepStrictEqual(wasm.listInRecord2(), { a: "list_in_record2" });

  assert.deepStrictEqual(
    wasm.listInRecord3({ a: "list_in_record3 input" }),
    { a: "list_in_record3 output" },
  );

  assert.deepStrictEqual(
    wasm.listInRecord4({ a: "input4" }),
    { a: "result4" },
  );

  wasm.listInVariant1("foo", { tag: 'err', val: 'bar' }, { tag: '0', val: 'baz' });

  assert.deepStrictEqual(wasm.listInVariant2(), "list_in_variant2");
  assert.deepStrictEqual(wasm.listInVariant3("input3"), "output3");

  assert.deepStrictEqual(wasm.errnoResult().tag, 'err');

  const [r1, r2] = wasm.listTypedefs("typedef1", ["typedef2"]);
  assert.deepStrictEqual(r1, (new TextEncoder()).encode('typedef3'));
  assert.deepStrictEqual(r2, ['typedef4']);
}

function testHandles(wasm: exports.Wasm) {
  const bytes = wasm.allocatedBytes();

  // Param/result of a handle works in a simple fashion
  const s: exports.WasmState = wasm.wasmStateCreate();
  assert.strictEqual(wasm.wasmStateGetVal(s), 100);

  // Deterministic destruction is possible
  assert.strictEqual(wasm.wasmState2SawClose(), false);
  const s2: exports.WasmState2 = wasm.wasmState2Create();
  assert.strictEqual(wasm.wasmState2SawClose(), false);
  s2.drop();
  assert.strictEqual(wasm.wasmState2SawClose(), true);

  const arg1 = wasm.wasmStateCreate();
  const arg2 = wasm.wasmState2Create();
  const [c, d] = wasm.twoWasmStates(arg1, arg2);
  arg1.drop();
  arg2.drop();

  wasm.wasmState2ParamRecord({ a: d });
  wasm.wasmState2ParamTuple([d]);
  wasm.wasmState2ParamOption(d);
  wasm.wasmState2ParamOption(null);
  wasm.wasmState2ParamResult({ tag: 'ok', val: d });
  wasm.wasmState2ParamResult({ tag: 'err', val: 2 });
  wasm.wasmState2ParamVariant({ tag: '0', val: d });
  wasm.wasmState2ParamVariant({ tag: '1', val: 2 });
  wasm.wasmState2ParamList([]);
  wasm.wasmState2ParamList([d]);
  wasm.wasmState2ParamList([d, d]);

  c.drop();
  d.drop();

  wasm.wasmState2ResultRecord().a.drop();
  wasm.wasmState2ResultTuple()[0].drop();
  const opt = wasm.wasmState2ResultOption();
  if (opt === null)
    throw new Error('should be some');
  opt.drop();
  const result = wasm.wasmState2ResultResult();
  if (result.tag === 'err')
    throw new Error('should be ok');
  result.val.drop();
  const variant = wasm.wasmState2ResultVariant();
  if (variant.tag === '1')
    throw new Error('should be 0');
  variant.val.drop();
  for (let val of wasm.wasmState2ResultList())
    val.drop();

  s.drop();
  assert.strictEqual(bytes, wasm.allocatedBytes());

  const md = exports.Markdown.create(wasm);
  if (md) {
    md.append("red is the best color");
    assert.strictEqual(md.render(), "green is the best color");
    md.drop();
  }
}

// fn buffers(wasm: &Wasm) -> Result<()> {
//     let mut out = [0; 10];
//     let n = wasm.buffer_u8(&[0u8], &mut out)? as usize;
//     assert_eq!(n, 3);
//     assert_eq!(&out[..n], [1, 2, 3]);
//     assert!(out[n..].iter().all(|x| *x == 0));

//     let mut out = [0; 10];
//     let n = wasm.buffer_u32(&[0], &mut out)? as usize;
//     assert_eq!(n, 3);
//     assert_eq!(&out[..n], [1, 2, 3]);
//     assert!(out[n..].iter().all(|x| *x == 0));

//     assert_eq!(wasm.buffer_bool(&mut iter::empty(), &mut Vec::new())?, 0);
//     assert_eq!(wasm.buffer_string(&mut iter::empty(), &mut Vec::new())?, 0);
//     assert_eq!(
//         wasm.buffer_list_bool(&mut iter::empty(), &mut Vec::new())?,
//         0
//     );

//     let mut bools = [true, false, true].iter().copied();
//     let mut out = Vec::with_capacity(4);
//     let n = wasm.buffer_bool(&mut bools, &mut out)?;
//     assert_eq!(n, 3);
//     assert_eq!(out, [false, true, false]);

//     let mut strings = ["foo", "bar", "baz"].iter().copied();
//     let mut out = Vec::with_capacity(3);
//     let n = wasm.buffer_string(&mut strings, &mut out)?;
//     assert_eq!(n, 3);
//     assert_eq!(out, ["FOO", "BAR", "BAZ"]);

//     let a = &[true, false, true][..];
//     let b = &[false, false][..];
//     let list = [a, b];
//     let mut lists = list.iter().copied();
//     let mut out = Vec::with_capacity(4);
//     let n = wasm.buffer_list_bool(&mut lists, &mut out)?;
//     assert_eq!(n, 2);
//     assert_eq!(out, [vec![false, true, false], vec![true, true]]);

//     let a = [true, false, true, true, false];
//     // let mut bools = a.iter().copied();
//     // let mut list = [&mut bools as &mut dyn ExactSizeIterator<Item = _>];
//     // let mut buffers = list.iter_mut().map(|b| &mut **b);
//     // wasm.buffer_buffer_bool(&mut buffers)?;

//     let mut bools = a.iter().copied();
//     wasm.buffer_mutable1(&mut [&mut bools])?;

//     let mut dst = [0; 10];
//     let n = wasm.buffer_mutable2(&mut [&mut dst])? as usize;
//     assert_eq!(n, 4);
//     assert_eq!(&dst[..n], [1, 2, 3, 4]);

//     let mut out = Vec::with_capacity(10);
//     let n = wasm.buffer_mutable3(&mut [&mut out])?;
//     assert_eq!(n, 3);
//     assert_eq!(out, [false, true, false]);

//     Ok(())
// }

function testInvalid(wasm: exports.Wasm) {
  const exports = wasm.instance.exports as any;
  assert.throws(exports.invalid_bool, /invalid variant discriminant for bool/);
  assert.throws(exports.invalid_u8, /must be between/);
  assert.throws(exports.invalid_s8, /must be between/);
  assert.throws(exports.invalid_u16, /must be between/);
  assert.throws(exports.invalid_s16, /must be between/);
  assert.throws(exports.invalid_char, /not a valid char/);
  assert.throws(exports.invalid_e1, /invalid discriminant specified for E1/);
  assert.throws(exports.invalid_handle, /handle index not valid/);
  assert.throws(exports.invalid_handle_close, /handle index not valid/);
}

await run()
