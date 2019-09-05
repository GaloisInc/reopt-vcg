def dpps1 : instruction :=
  definst "dpps" $ do
    pattern fun (v_2851 : imm int) (v_2853 : reg (bv 128)) (v_2854 : reg (bv 128)) => do
      v_4681 <- eval (handleImmediateWithSignExtend v_2851 8 8);
      v_4684 <- getRegister v_2854;
      v_4687 <- getRegister v_2853;
      v_4728 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4681 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4684 96 128) 24 8) (MInt2Float (extract v_4687 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4681 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4684 64 96) 24 8) (MInt2Float (extract v_4687 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4681 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4684 32 64) 24 8) (MInt2Float (extract v_4687 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4681 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4684 0 32) 24 8) (MInt2Float (extract v_4687 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2854) (concat (concat (concat (mux (isBitSet v_4681 4) v_4728 (expression.bv_nat 32 0)) (mux (isBitSet v_4681 5) v_4728 (expression.bv_nat 32 0))) (mux (isBitSet v_4681 6) v_4728 (expression.bv_nat 32 0))) (mux (isBitSet v_4681 7) v_4728 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2847 : imm int) (v_2846 : Mem) (v_2848 : reg (bv 128)) => do
      v_8188 <- eval (handleImmediateWithSignExtend v_2847 8 8);
      v_8191 <- getRegister v_2848;
      v_8194 <- evaluateAddress v_2846;
      v_8195 <- load v_8194 16;
      v_8236 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8188 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8191 96 128) 24 8) (MInt2Float (extract v_8195 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_8188 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8191 64 96) 24 8) (MInt2Float (extract v_8195 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8188 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8191 32 64) 24 8) (MInt2Float (extract v_8195 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_8188 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8191 0 32) 24 8) (MInt2Float (extract v_8195 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2848) (concat (concat (concat (mux (isBitSet v_8188 4) v_8236 (expression.bv_nat 32 0)) (mux (isBitSet v_8188 5) v_8236 (expression.bv_nat 32 0))) (mux (isBitSet v_8188 6) v_8236 (expression.bv_nat 32 0))) (mux (isBitSet v_8188 7) v_8236 (expression.bv_nat 32 0)));
      pure ()
    pat_end
