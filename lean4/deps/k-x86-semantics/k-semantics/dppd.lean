def dppd1 : instruction :=
  definst "dppd" $ do
    pattern fun (v_2787 : imm int) (v_2790 : reg (bv 128)) (v_2791 : reg (bv 128)) => do
      v_4770 <- eval (handleImmediateWithSignExtend v_2787 8 8);
      v_4775 <- getRegister v_2791;
      v_4776 <- eval (extract v_4775 64 128);
      v_4784 <- getRegister v_2790;
      v_4785 <- eval (extract v_4784 64 128);
      v_4799 <- eval (extract v_4775 0 64);
      v_4807 <- eval (extract v_4784 0 64);
      v_4820 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4770 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4776 0 1)) (uvalueMInt (extract v_4776 1 12)) (uvalueMInt (extract v_4776 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4785 0 1)) (uvalueMInt (extract v_4785 1 12)) (uvalueMInt (extract v_4785 12 64)))) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_4770 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4799 0 1)) (uvalueMInt (extract v_4799 1 12)) (uvalueMInt (extract v_4799 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4807 0 1)) (uvalueMInt (extract v_4807 1 12)) (uvalueMInt (extract v_4807 12 64)))) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2791) (concat (mux (eq (extract v_4770 6 7) (expression.bv_nat 1 1)) v_4820 (expression.bv_nat 64 0)) (mux (eq (extract v_4770 7 8) (expression.bv_nat 1 1)) v_4820 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2782 : imm int) (v_2783 : Mem) (v_2785 : reg (bv 128)) => do
      v_8784 <- eval (handleImmediateWithSignExtend v_2782 8 8);
      v_8789 <- getRegister v_2785;
      v_8790 <- eval (extract v_8789 64 128);
      v_8798 <- evaluateAddress v_2783;
      v_8799 <- load v_8798 16;
      v_8800 <- eval (extract v_8799 64 128);
      v_8814 <- eval (extract v_8789 0 64);
      v_8822 <- eval (extract v_8799 0 64);
      v_8835 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8784 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8790 0 1)) (uvalueMInt (extract v_8790 1 12)) (uvalueMInt (extract v_8790 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8800 0 1)) (uvalueMInt (extract v_8800 1 12)) (uvalueMInt (extract v_8800 12 64)))) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_8784 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8814 0 1)) (uvalueMInt (extract v_8814 1 12)) (uvalueMInt (extract v_8814 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8822 0 1)) (uvalueMInt (extract v_8822 1 12)) (uvalueMInt (extract v_8822 12 64)))) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_2785) (concat (mux (eq (extract v_8784 6 7) (expression.bv_nat 1 1)) v_8835 (expression.bv_nat 64 0)) (mux (eq (extract v_8784 7 8) (expression.bv_nat 1 1)) v_8835 (expression.bv_nat 64 0)));
      pure ()
    pat_end
