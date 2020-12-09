
import MCInst.InstParser

namespace x86
namespace mcinst

-- Handling the result of decoding
@[reducible]
def decode_result := Sum Nat (String × Nat)

@[export mcinst_exported_mk_decode_success]
def mk_decode_success (i : String) (nbytes : Nat) : decode_result := Sum.inr (i, nbytes)

@[export mcinst_exported_mk_decode_failure]
def mk_decode_failure (nbytes : Nat) : decode_result := Sum.inl nbytes

namespace prim

-- Imported (FFI) functions
@[extern "vadd_mcinst_decode"]
def decode ( b : @& ByteArray ) (offset : @& Nat) (vaddr : @& Nat) : decode_result := arbitrary

end prim

structure decoder :=
  (bytes : ByteArray)
  (vaddr : Nat)

def mk_decoder (bs : ByteArray) (v : Nat) : decoder :=
  decoder.mk bs v

def decode (d : decoder) (v : Nat) : Sum Nat (instruction × Nat) :=
  if v < d.vaddr
  then Sum.inl 0 
  else match prim.decode d.bytes (v - d.vaddr) d.vaddr with
       | Sum.inl n => Sum.inl n
       | Sum.inr (i, n) =>
          match parse i with 
          | some r => Sum.inr (r, n)
          | _      => Sum.inl 0

end mcinst
end x86
