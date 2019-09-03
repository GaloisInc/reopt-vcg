def cmovgq1 : instruction :=
  definst "cmovgq" $ do
    pattern fun (v_2621 : reg (bv 64)) (v_2622 : reg (bv 64)) => do
      v_4319 <- getRegister zf;
      v_4322 <- getRegister sf;
      v_4324 <- getRegister of;
      v_4328 <- getRegister v_2621;
      v_4329 <- getRegister v_2622;
      setRegister (lhs.of_reg v_2622) (mux (bit_and (notBool_ (eq v_4319 (expression.bv_nat 1 1))) (eq (eq v_4322 (expression.bv_nat 1 1)) (eq v_4324 (expression.bv_nat 1 1)))) v_4328 v_4329);
      pure ()
    pat_end;
    pattern fun (v_2616 : Mem) (v_2617 : reg (bv 64)) => do
      v_8003 <- getRegister zf;
      v_8006 <- getRegister sf;
      v_8008 <- getRegister of;
      v_8012 <- evaluateAddress v_2616;
      v_8013 <- load v_8012 8;
      v_8014 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2617) (mux (bit_and (notBool_ (eq v_8003 (expression.bv_nat 1 1))) (eq (eq v_8006 (expression.bv_nat 1 1)) (eq v_8008 (expression.bv_nat 1 1)))) v_8013 v_8014);
      pure ()
    pat_end
