def dppd1 : instruction :=
  definst "dppd" $ do
    pattern fun (v_2778 : imm int) (v_2776 : reg (bv 128)) (v_2777 : reg (bv 128)) => do
      v_4654 <- eval (handleImmediateWithSignExtend v_2778 8 8);
      v_4659 <- getRegister v_2777;
      v_4662 <- getRegister v_2776;
      v_4680 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4654 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4659 64 128) 53 11) (MInt2Float (extract v_4662 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_4654 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4659 0 64) 53 11) (MInt2Float (extract v_4662 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2777) (concat (mux (eq (extract v_4654 6 7) (expression.bv_nat 1 1)) v_4680 (expression.bv_nat 64 0)) (mux (eq (extract v_4654 7 8) (expression.bv_nat 1 1)) v_4680 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2773 : imm int) (v_2771 : Mem) (v_2772 : reg (bv 128)) => do
      v_8380 <- eval (handleImmediateWithSignExtend v_2773 8 8);
      v_8385 <- getRegister v_2772;
      v_8388 <- evaluateAddress v_2771;
      v_8389 <- load v_8388 16;
      v_8407 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8380 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8385 64 128) 53 11) (MInt2Float (extract v_8389 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_8380 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8385 0 64) 53 11) (MInt2Float (extract v_8389 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2772) (concat (mux (eq (extract v_8380 6 7) (expression.bv_nat 1 1)) v_8407 (expression.bv_nat 64 0)) (mux (eq (extract v_8380 7 8) (expression.bv_nat 1 1)) v_8407 (expression.bv_nat 64 0)));
      pure ()
    pat_end
