def dpps : instruction :=
  definst "dpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      v_7 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_3 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 96 128) 24 8) (MInt2Float (extract v_6 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_3 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 64 96) 24 8) (MInt2Float (extract v_6 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_3 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 32 64) 24 8) (MInt2Float (extract v_6 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_3 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 0 32) 24 8) (MInt2Float (extract v_6 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) v_7 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_7 (expression.bv_nat 32 0))) (mux (isBitSet v_3 6) v_7 (expression.bv_nat 32 0))) (mux (isBitSet v_3 7) v_7 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_3 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 96 128) 24 8) (MInt2Float (extract v_5 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_3 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 64 96) 24 8) (MInt2Float (extract v_5 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_3 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 32 64) 24 8) (MInt2Float (extract v_5 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_3 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4 0 32) 24 8) (MInt2Float (extract v_5 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) v_6 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_6 (expression.bv_nat 32 0))) (mux (isBitSet v_3 6) v_6 (expression.bv_nat 32 0))) (mux (isBitSet v_3 7) v_6 (expression.bv_nat 32 0)));
      pure ()
    pat_end
