def cmovngw1 : instruction :=
  definst "cmovngw" $ do
    pattern fun (v_2937 : reg (bv 16)) (v_2938 : reg (bv 16)) => do
      v_4763 <- getRegister zf;
      v_4765 <- getRegister sf;
      v_4767 <- getRegister of;
      v_4772 <- getRegister v_2937;
      v_4773 <- getRegister v_2938;
      setRegister (lhs.of_reg v_2938) (mux (bit_or (eq v_4763 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4765 (expression.bv_nat 1 1)) (eq v_4767 (expression.bv_nat 1 1))))) v_4772 v_4773);
      pure ()
    pat_end;
    pattern fun (v_2931 : Mem) (v_2933 : reg (bv 16)) => do
      v_8302 <- getRegister zf;
      v_8304 <- getRegister sf;
      v_8306 <- getRegister of;
      v_8311 <- evaluateAddress v_2931;
      v_8312 <- load v_8311 2;
      v_8313 <- getRegister v_2933;
      setRegister (lhs.of_reg v_2933) (mux (bit_or (eq v_8302 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8304 (expression.bv_nat 1 1)) (eq v_8306 (expression.bv_nat 1 1))))) v_8312 v_8313);
      pure ()
    pat_end
