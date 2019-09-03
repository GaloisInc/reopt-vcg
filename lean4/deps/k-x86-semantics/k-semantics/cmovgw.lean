def cmovgw1 : instruction :=
  definst "cmovgw" $ do
    pattern fun (v_2643 : reg (bv 16)) (v_2644 : reg (bv 16)) => do
      v_4349 <- getRegister zf;
      v_4352 <- getRegister sf;
      v_4354 <- getRegister of;
      v_4358 <- getRegister v_2643;
      v_4359 <- getRegister v_2644;
      setRegister (lhs.of_reg v_2644) (mux (bit_and (notBool_ (eq v_4349 (expression.bv_nat 1 1))) (eq (eq v_4352 (expression.bv_nat 1 1)) (eq v_4354 (expression.bv_nat 1 1)))) v_4358 v_4359);
      pure ()
    pat_end;
    pattern fun (v_2637 : Mem) (v_2639 : reg (bv 16)) => do
      v_7990 <- getRegister zf;
      v_7993 <- getRegister sf;
      v_7995 <- getRegister of;
      v_7999 <- evaluateAddress v_2637;
      v_8000 <- load v_7999 2;
      v_8001 <- getRegister v_2639;
      setRegister (lhs.of_reg v_2639) (mux (bit_and (notBool_ (eq v_7990 (expression.bv_nat 1 1))) (eq (eq v_7993 (expression.bv_nat 1 1)) (eq v_7995 (expression.bv_nat 1 1)))) v_8000 v_8001);
      pure ()
    pat_end
