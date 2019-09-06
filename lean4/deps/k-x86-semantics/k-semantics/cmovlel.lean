def cmovlel1 : instruction :=
  definst "cmovlel" $ do
    pattern fun (v_2739 : reg (bv 32)) (v_2740 : reg (bv 32)) => do
      v_4411 <- getRegister zf;
      v_4412 <- getRegister sf;
      v_4413 <- getRegister of;
      v_4417 <- getRegister v_2739;
      v_4418 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2740) (mux (bit_or v_4411 (notBool_ (eq v_4412 v_4413))) v_4417 v_4418);
      pure ()
    pat_end;
    pattern fun (v_2728 : Mem) (v_2731 : reg (bv 32)) => do
      v_7833 <- getRegister zf;
      v_7834 <- getRegister sf;
      v_7835 <- getRegister of;
      v_7839 <- evaluateAddress v_2728;
      v_7840 <- load v_7839 4;
      v_7841 <- getRegister v_2731;
      setRegister (lhs.of_reg v_2731) (mux (bit_or v_7833 (notBool_ (eq v_7834 v_7835))) v_7840 v_7841);
      pure ()
    pat_end
