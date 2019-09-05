def cmovleq1 : instruction :=
  definst "cmovleq" $ do
    pattern fun (v_2727 : reg (bv 64)) (v_2728 : reg (bv 64)) => do
      v_4444 <- getRegister zf;
      v_4446 <- getRegister sf;
      v_4448 <- getRegister of;
      v_4453 <- getRegister v_2727;
      v_4454 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2728) (mux (bit_or (eq v_4444 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4446 (expression.bv_nat 1 1)) (eq v_4448 (expression.bv_nat 1 1))))) v_4453 v_4454);
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) (v_2719 : reg (bv 64)) => do
      v_8033 <- getRegister zf;
      v_8035 <- getRegister sf;
      v_8037 <- getRegister of;
      v_8042 <- evaluateAddress v_2718;
      v_8043 <- load v_8042 8;
      v_8044 <- getRegister v_2719;
      setRegister (lhs.of_reg v_2719) (mux (bit_or (eq v_8033 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8035 (expression.bv_nat 1 1)) (eq v_8037 (expression.bv_nat 1 1))))) v_8043 v_8044);
      pure ()
    pat_end
