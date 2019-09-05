def cmovgw1 : instruction :=
  definst "cmovgw" $ do
    pattern fun (v_2693 : reg (bv 16)) (v_2694 : reg (bv 16)) => do
      v_4400 <- getRegister zf;
      v_4403 <- getRegister sf;
      v_4405 <- getRegister of;
      v_4409 <- getRegister v_2693;
      v_4410 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2694) (mux (bit_and (notBool_ (eq v_4400 (expression.bv_nat 1 1))) (eq (eq v_4403 (expression.bv_nat 1 1)) (eq v_4405 (expression.bv_nat 1 1)))) v_4409 v_4410);
      pure ()
    pat_end;
    pattern fun (v_2688 : Mem) (v_2689 : reg (bv 16)) => do
      v_8003 <- getRegister zf;
      v_8006 <- getRegister sf;
      v_8008 <- getRegister of;
      v_8012 <- evaluateAddress v_2688;
      v_8013 <- load v_8012 2;
      v_8014 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2689) (mux (bit_and (notBool_ (eq v_8003 (expression.bv_nat 1 1))) (eq (eq v_8006 (expression.bv_nat 1 1)) (eq v_8008 (expression.bv_nat 1 1)))) v_8013 v_8014);
      pure ()
    pat_end
