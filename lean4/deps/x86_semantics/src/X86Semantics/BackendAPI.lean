
import X86Semantics.Common

namespace x86

open mc_semantics
open mc_semantics.type

structure Backend : Type 1 :=
  -- Symbolic types
  (s_bv : Nat -> Type)
  (s_bool : Type)

  -- injections
  (s_bv_imm     (n : Nat) : Nat  -> s_bv n)
  (s_bool_imm           : Bool -> s_bool)

  -- Underlying monad.
  (monad : Type -> Type)
  [Monad_backend : Monad monad]
  [MonadExcept_backend : MonadExcept String monad]

  -- Memory operations
  (store_word (n : Nat) (addr : s_bv 64) (b : s_bv (8 * n)) : monad Unit)
  -- Option here as reading can fail, but this might be total for the smt backend
  (read_word (addr : s_bv 64) (n : Nat) : monad (s_bv (8 * n)))

  -- Register operations
  (get_gpreg : Fin 16            -> monad (s_bv 64))
  (set_gpreg : Fin 16 -> s_bv 64 -> monad Unit)
  (get_flag  : Fin 32            -> monad s_bool)
  (set_flag  : Fin 32 -> s_bool  -> monad Unit)
  (get_avxreg : Fin 16            -> monad (s_bv 256))
  (set_avxreg : Fin 16 -> s_bv 256 -> monad Unit)

  -- Value operations
  -- FIXME: should these reside inside a monad?

  -- Symbolic bool operations
  -- monomorphic to avoid s_ite b (21 : Nat) (32 : Nat)
  (s_mux_bool         : s_bool -> s_bool -> s_bool -> s_bool) 
  (s_mux_bv {n : Nat} : s_bool -> s_bv n -> s_bv n -> s_bv n)
  -- Mainly for cond_set, useful for cond jump as well
  -- FIXME: replace by mux_set_reg etc.
  (s_mux_m            : s_bool -> monad Unit -> monad Unit -> monad Unit)
  
  (s_not              : s_bool -> s_bool) 
  (s_or               : s_bool -> s_bool -> s_bool)
  (s_and              : s_bool -> s_bool -> s_bool) 
  (s_xor              : s_bool -> s_bool -> s_bool)
 
  -- Symbolic bv operations
  -- - Comparison
  (s_bveq   {n : Nat} : s_bv n -> s_bv n -> s_bool)
  (s_bvult  {n : Nat} : s_bv n -> s_bv n -> s_bool)
  (s_bvslt  {n : Nat} : s_bv n -> s_bv n -> s_bool)
  
  -- - Arithmetic
  (s_bvneg  (n : Nat) : s_bv n -> s_bv n)
  (s_bvnot  (n : Nat) : s_bv n -> s_bv n)

  (s_bvadd  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvsub  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvmul  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvudiv (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvurem (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  -- FIXME: add proof args?
  (s_bvextract (n i j : Nat ) : s_bv n -> s_bv (i + 1 - j))
  (s_sext    (n m : Nat) : s_bv n -> s_bv m)
  (s_uext    (n m : Nat) : s_bv n -> s_bv m)
  (s_trunc   (n m : Nat) : s_bv n -> s_bv m)
  (s_bvappend {n : Nat} {m : Nat} : s_bv n -> s_bv m -> s_bv (n + m))
  (s_bvgetbits  {n : Nat} (off m : Nat) : s_bv n -> s_bv m)
  (s_bvsetbits  {n m : Nat} (off : Nat) : s_bv n -> s_bv m -> s_bv n)
  (s_bvand  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvor   (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvxor  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvshl  (n : Nat) : s_bv n -> s_bv n -> s_bv n)
  (s_bvmsb  (n : Nat) : s_bv n -> s_bool)
  -- unsigned
  (s_bvlshr {n : Nat} : s_bv n -> s_bv n -> s_bv n)
  -- signed
  (s_bvsshr {n : Nat} : s_bv n -> s_bv n -> s_bv n)
  (s_parity {n : Nat} : s_bv n -> s_bool)
  (s_bit_test {wr wi : Nat} : s_bv wr -> s_bv wi -> s_bool)

  -- System operations
  (s_os_transition : monad Unit)
  (s_get_ip : monad (s_bv 64))
  (s_set_ip : s_bv 64 -> monad Unit)
  (s_cond_set_ip : s_bool -> s_bv 64 -> monad Unit) -- We could combine this with the above.

  -- (s_cond_set_ip : s_bool -> s_bv 64 -> monad Unit)
  (s_read_cpuid : monad Unit)

namespace Backend

def s_bvzero (be : Backend) (n : Nat) : be.s_bv n := be.s_bv_imm n 0

def machine_word (be : Backend) : Type := be.s_bv 64

def s_bool_eq (be : Backend) (b1 : be.s_bool) (b2 : be.s_bool) :=
  be.s_mux_bool b1 b2 (be.s_not b2)

def false (be : Backend) : be.s_bool := be.s_bool_imm false
def true (be : Backend) : be.s_bool := be.s_bool_imm true

def bit_to_bitvec (be : Backend) (n : Nat) (b : be.s_bool) : be.s_bv n := 
  be.s_mux_bv b (be.s_bv_imm n 1) (be.s_bv_imm n 0)
 
end Backend
end x86
