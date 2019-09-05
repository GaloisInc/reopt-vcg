def dppd1 : instruction :=
  definst "dppd" $ do
    pattern fun (v_2840 : imm int) (v_2842 : reg (bv 128)) (v_2843 : reg (bv 128)) => do
      v_4647 <- eval (handleImmediateWithSignExtend v_2840 8 8);
      v_4650 <- getRegister v_2843;
      v_4653 <- getRegister v_2842;
      v_4670 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4647 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4650 64 128) 53 11) (MInt2Float (extract v_4653 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_4647 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4650 0 64) 53 11) (MInt2Float (extract v_4653 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2843) (concat (mux (isBitSet v_4647 6) v_4670 (expression.bv_nat 64 0)) (mux (isBitSet v_4647 7) v_4670 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2836 : imm int) (v_2835 : Mem) (v_2837 : reg (bv 128)) => do
      v_8158 <- eval (handleImmediateWithSignExtend v_2836 8 8);
      v_8161 <- getRegister v_2837;
      v_8164 <- evaluateAddress v_2835;
      v_8165 <- load v_8164 16;
      v_8182 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8158 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8161 64 128) 53 11) (MInt2Float (extract v_8165 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_8158 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8161 0 64) 53 11) (MInt2Float (extract v_8165 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2837) (concat (mux (isBitSet v_8158 6) v_8182 (expression.bv_nat 64 0)) (mux (isBitSet v_8158 7) v_8182 (expression.bv_nat 64 0)));
      pure ()
    pat_end
