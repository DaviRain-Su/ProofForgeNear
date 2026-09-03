import ProofForge

/-!
Cryptographic host fixture: view-safe hashes plus mutating ecrecover / ed25519_verify
and keccak512 scenes. Hash windows are little-endian packs of host digest bytes.
-/
namespace Examples.Near.NearCrypto
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Hash

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def abc : BoundedBytes 8 :=
  { length := 3, values := #v[97, 98, 99, 0, 0, 0, 0, 0] }

@[pf_inline] def abd : BoundedBytes 8 :=
  { length := 3, values := #v[97, 98, 100, 0, 0, 0, 0, 0] }

@[pf_entry]
def init : State :=
  { stamped := 0 }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

/-- view：sha256("abc") 第 0 个小端窗口。 -/
@[pf_entry]
def sha256W0 (_s : State) : UInt64 :=
  let buf : Sha256 := 32
  let _ := buf.hash abc
  buf.w0

/-- view：sha256("abc") 最高窗口。 -/
@[pf_entry]
def sha256W3 (_s : State) : UInt64 :=
  let buf : Sha256 := 32
  let _ := buf.hash abc
  buf.w3

/-- view：keccak256("abc") 第 0 个小端窗口。 -/
@[pf_entry]
def keccak256W0 (_s : State) : UInt64 :=
  let buf : Keccak256 := 32
  let _ := buf.hash abc
  buf.w0

/-- view：ripemd160("abc") 第 0 个小端窗口。 -/
@[pf_entry]
def ripemd160W0 (_s : State) : UInt64 :=
  let buf : Ripemd160 := 20
  let _ := buf.hash abc
  buf.w0

/-- view：ripemd160("abc") 最后 4 字节零填充窗口。 -/
@[pf_entry]
def ripemd160W2 (_s : State) : UInt64 :=
  let buf : Ripemd160 := 20
  let _ := buf.hash abc
  buf.w2

/-- 入口：keccak512("abc") 前 8 字节。view-safe 但放在 mutating 项上。 -/
@[pf_entry]
def keccak512W0 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let buf : Keccak512 := 64
    let _ := buf.hash abc
    let w := buf.w0
    .ok ({ stamped := w }, w)
  else
    .error .overflow

/-- sha256("hello") as four little-endian windows. -/
@[pf_inline] def helloHash : CryptoBytes32 :=
  { w0 := 0x0ea3b05fba4df22c, w1 := 0x9ee2b9c52a3be826
    w2 := 0x5e42a71f5c1e161b, w3 := 0x24988b9362330473 }

/-- secp256k1 signature (r||s) for private key 1 over sha256("hello"). -/
@[pf_inline] def helloSig : CryptoBytes64 :=
  { w0 := 0x61c265d351a76d26, w1 := 0x5a674c95643b52bd
    w2 := 0x4522d234eda1aa95, w3 := 0xd4cb07ea0b9658ea
    w4 := 0x084d3ea673186c96, w5 := 0x553ae661f367391e
    w6 := 0x203d1218c4cfad73, w7 := 0xca01daff4fc844f5 }

/-- RFC 8032 test-1 public key. -/
@[pf_inline] def rfcPk : CryptoBytes32 :=
  { w0 := 0xb70ab18201985ad7, w1 := 0x3a0764c9d3fe4bd5
    w2 := 0x2523a6daf372e10e, w3 := 0x1a5107f7681a02af }

/-- RFC 8032 test-1 secret signing "abc". -/
@[pf_inline] def rfcSigAbc : CryptoBytes64 :=
  { w0 := 0x60a27c1eb024d780, w1 := 0x735fc9e78d7fccf4
    w2 := 0x2b761fab5b61accf, w3 := 0x6dcfc826ecb63564
    w4 := 0x9a39872fae8d752c, w5 := 0xac3528cdcba1ed8e
    w6 := 0xa5aba3ca6e6da65b, w7 := 0x07c23d0551a767e5 }

/-- 入口：ecrecover status。失败 status≠0 且 limbs 清零。 -/
@[pf_entry]
def ecrecoverStatus (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 0 0
    let st := ProofForge.Wasm.Near.Runtime.ecrecoverStatus 64
    .ok ({ stamped := st }, st)
  else
    .error .overflow

/-- 入口：ecrecover 恢复公钥第 0 窗口。 -/
@[pf_entry]
def ecrecoverW0 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 0 0
    let w := ProofForge.Wasm.Near.Runtime.ecrecoverResultW0 64
    .ok ({ stamped := w }, w)
  else
    .error .overflow

/-- 入口：ecrecover 恢复公钥最高窗口。 -/
@[pf_entry]
def ecrecoverW7 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 0 0
    let w := ProofForge.Wasm.Near.Runtime.ecrecoverResultW7 64
    .ok ({ stamped := w }, w)
  else
    .error .overflow

/-- Same ecrecover with v=1. -/
@[pf_entry]
def ecrecoverStatus1 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 1 0
    let st := ProofForge.Wasm.Near.Runtime.ecrecoverStatus 64
    .ok ({ stamped := st }, st)
  else
    .error .overflow

@[pf_entry]
def ecrecoverW0v1 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 1 0
    let w := ProofForge.Wasm.Near.Runtime.ecrecoverResultW0 64
    .ok ({ stamped := w }, w)
  else
    .error .overflow

@[pf_entry]
def ecrecoverW7v1 (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ecrecover 64 helloHash helloSig 1 0
    let w := ProofForge.Wasm.Near.Runtime.ecrecoverResultW7 64
    .ok ({ stamped := w }, w)
  else
    .error .overflow

/-- 入口：ed25519_verify 消息 "abc"。 -/
@[pf_entry]
def ed25519Abc (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ed25519Verify 8 8 rfcSigAbc abc rfcPk
    let ok := ProofForge.Wasm.Near.Runtime.ed25519VerifyOk 8
    .ok ({ stamped := ok }, ok)
  else
    .error .overflow

/-- 入口：同一签名对篡改消息 "abd"。 -/
@[pf_entry]
def ed25519Abd (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Wasm.Near.Runtime.ed25519Verify 8 8 rfcSigAbc abd rfcPk
    let ok := ProofForge.Wasm.Near.Runtime.ed25519VerifyOk 8
    .ok ({ stamped := ok }, ok)
  else
    .error .overflow

end Examples.Near.NearCrypto
