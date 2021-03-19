
import X86Semantics.Common

namespace x86

open mc_semantics
open mc_semantics.type

structure Backend : Type 1 :=
  -- Symbolic types
  (s_bv : Nat -> Type)
  (s_bool : Type)
  (s_float : float_class -> Type)

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
  -- (set_gpreg : Fin 16 -> s_bv 64 -> monad Unit)
  (s_cond_set_gpreg  : s_bool -> Fin 16 -> s_bv 64 -> monad Unit)

  (get_flag  : Fin 32            -> monad s_bool)
  -- (set_flag  : Fin 32 -> s_bool  -> monad Unit)
  (s_cond_set_flag   : s_bool -> Fin 32 -> s_bool -> monad Unit)

  (get_avxreg : Fin 16            -> monad (s_bv avx_width))
  -- (set_avxreg : Fin 16 -> s_bv 256 -> monad Unit)
  (s_cond_set_avxreg : s_bool -> Fin 16 -> s_bv avx_width -> monad Unit)

  

  -- Value operations
  -- FIXME: should these reside inside a monad?

  -- Symbolic bool operations
  -- monomorphic to avoid s_ite b (21 : Nat) (32 : Nat)
  (s_mux_bool         : s_bool -> s_bool -> s_bool -> s_bool) 
  (s_mux_bv {n : Nat} : s_bool -> s_bv n -> s_bv n -> s_bv n)
  (s_mux_float {fc : float_class} : s_bool -> s_float fc -> s_float fc -> s_float fc)
  
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

  -- Floating point
  (s_fp_literal : forall (fc : float_class) (m : Nat) (esign : Bool) (e : Nat), s_float fc)
  (s_bv_bitcast_to_fp : forall (fc : float_class), s_bv fc.width -> s_float fc)
  (s_fp_bitcast_to_bv : forall (fc : float_class), s_float fc -> s_bv fc.width)
  (s_fp_convert_to_fp : forall (sfc dfc : float_class) (rm : RoundingMode), s_float sfc -> s_float dfc)

  (s_fp_convert_to_int : forall (fc : float_class) (is32or64 : Bool) (rm : RoundingMode), s_float fc -> 
                                s_bv (if is32or64 then 32 else 64))

  (s_int_convert_to_fp : forall (fc : float_class) (is32or64 : Bool),
                                s_bv (if is32or64 then 32 else 64) -> s_float fc)

  (s_fp_add : forall (fc : float_class), s_float fc -> s_float fc -> s_float fc)
  (s_fp_sub : forall (fc : float_class), s_float fc -> s_float fc -> s_float fc)
  (s_fp_mul : forall (fc : float_class), s_float fc -> s_float fc -> s_float fc)
  (s_fp_div : forall (fc : float_class), s_float fc -> s_float fc -> s_float fc)
  (s_fp_sqrt : forall (fc : float_class), s_float fc -> s_float fc)

  (s_fp_le : forall (fc : float_class), s_float fc -> s_float fc -> s_bool)
  (s_fp_lt : forall (fc : float_class), s_float fc -> s_float fc -> s_bool)

  -- more complex than lt due to NaN etc.  These return 1 if the first is max/min the second
  (s_fp_max : forall (fc : float_class), s_float fc -> s_float fc -> s_bool)
  (s_fp_min : forall (fc : float_class), s_float fc -> s_float fc -> s_bool)
  (s_fp_ordered : forall (fc : float_class), s_float fc -> s_float fc -> s_bool)
  
  -- (s_cond_set_ip : s_bool -> s_bv 64 -> monad Unit)
  (s_read_cpuid : monad Unit)

namespace Backend

def s_bvzero (be : Backend) (n : Nat) : be.s_bv n := be.s_bv_imm n 0

def machine_word (be : Backend) : Type := be.s_bv 64

def s_bool_eq (be : Backend) (b1 : be.s_bool) (b2 : be.s_bool) :=
  be.s_mux_bool b1 b2 (be.s_not b2)

protected def false (be : Backend) : be.s_bool := be.s_bool_imm false
protected def true (be : Backend) : be.s_bool := be.s_bool_imm true

def bit_to_bitvec (be : Backend) (n : Nat) (b : be.s_bool) : be.s_bv n := 
  be.s_mux_bv b (be.s_bv_imm n 1) (be.s_bv_imm n 0)

-- number is - (m + 1).  Note (not x = neg x - 1)
def s_bv_imm_int (backend : Backend) (w : Nat) (i : Int) : backend.s_bv w :=
  match i with
  | Int.ofNat n   => backend.s_bv_imm w n
  | Int.negSucc m => backend.s_bvnot w (backend.s_bv_imm w m)

def set_gpreg (backend : Backend) (r : Fin 16) (v : backend.s_bv 64) : backend.monad Unit :=
  backend.s_cond_set_gpreg backend.true r v

def set_flag (backend : Backend) (r : Fin 32) (v : backend.s_bool) : backend.monad Unit :=
  backend.s_cond_set_flag backend.true r v

def set_avxreg (backend : Backend) (r : Fin 16) (v : backend.s_bv avx_width) : backend.monad Unit :=
  backend.s_cond_set_avxreg backend.true r v

 
end Backend

namespace reg


-- ------------------------------------------------------------------------------
-- Convenience functions in backend

section with_backend

variable {backend : Backend}


axiom inject_ax0 : 8 + gpreg_type.width gpreg_type.reg8h ≤ 64
axiom inject_ax1 : ∀(rtp : gpreg_type), 0 + gpreg_type.width rtp ≤ 64
axiom avx_inject_ax1 : ∀(rtp : avxreg_type), 0 + avxreg_type.width rtp ≤ 256

def inject : ∀(rtp : gpreg_type), backend.s_bv rtp.width -> backend.s_bv 64 -> backend.s_bv 64
  | gpreg_type.reg32, b, _   => backend.s_uext _ _ b
  | gpreg_type.reg8h, b, old => backend.s_bvsetbits 8 old b -- inject_ax0
  | gpreg_type.reg64, b, _   => b -- special case to keep output compact
  | rtp,              b, old => backend.s_bvsetbits 0 old b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

def project : ∀(rtp : gpreg_type), backend.s_bv 64 -> backend.s_bv rtp.width
  | gpreg_type.reg8h, b => backend.s_bvgetbits 8 8 b -- inject_ax0 -- (begin simp [gpreg_type.width], exact dec_trivial end)
  | gpreg_type.reg64, b => b -- special case to keep output compact
  | rtp,              b => backend.s_bvgetbits 0 rtp.width b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

-- FIXME: this depends on the mode, no? SSE instructions inject, while AVX clear upper bits
def avx_inject : ∀(rtp : avxreg_type), backend.s_bv rtp.width -> backend.s_bv avx_width -> backend.s_bv avx_width
  := fun rtp b old => backend.s_bvsetbits 0 old b -- (avx_inject_ax1 rtp) -- (begin cases rtp; simp end)

def avx_project : ∀(rtp : avxreg_type), backend.s_bv avx_width -> backend.s_bv rtp.width
    := fun rtp b =>  backend.s_bvgetbits 0 rtp.width b

end with_backend

end reg

end x86
