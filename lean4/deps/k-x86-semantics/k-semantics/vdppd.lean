def vdppd1 : instruction :=
  definst "vdppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      v_8 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 64 128) 53 11) (MInt2Float (extract v_7 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_4 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 0 64) 53 11) (MInt2Float (extract v_7 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_8 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_8 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- getRegister xmm_1;
      v_7 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 64 128) 53 11) (MInt2Float (extract v_6 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_4 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 0 64) 53 11) (MInt2Float (extract v_6 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_7 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_7 (expression.bv_nat 64 0)));
      pure ()
    pat_end
