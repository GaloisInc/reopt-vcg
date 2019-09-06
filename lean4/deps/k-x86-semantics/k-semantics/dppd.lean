def dppd1 : instruction :=
  definst "dppd" $ do
    pattern fun (v_2867 : imm int) (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) => do
      v_4668 <- eval (handleImmediateWithSignExtend v_2867 8 8);
      v_4671 <- getRegister v_2869;
      v_4674 <- getRegister v_2868;
      v_4691 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4668 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4671 64 128) 53 11) (MInt2Float (extract v_4674 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_4668 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4671 0 64) 53 11) (MInt2Float (extract v_4674 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2869) (concat (mux (isBitSet v_4668 6) v_4691 (expression.bv_nat 64 0)) (mux (isBitSet v_4668 7) v_4691 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2862 : imm int) (v_2863 : Mem) (v_2864 : reg (bv 128)) => do
      v_8168 <- eval (handleImmediateWithSignExtend v_2862 8 8);
      v_8171 <- getRegister v_2864;
      v_8174 <- evaluateAddress v_2863;
      v_8175 <- load v_8174 16;
      v_8192 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8168 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8171 64 128) 53 11) (MInt2Float (extract v_8175 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_8168 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8171 0 64) 53 11) (MInt2Float (extract v_8175 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2864) (concat (mux (isBitSet v_8168 6) v_8192 (expression.bv_nat 64 0)) (mux (isBitSet v_8168 7) v_8192 (expression.bv_nat 64 0)));
      pure ()
    pat_end
