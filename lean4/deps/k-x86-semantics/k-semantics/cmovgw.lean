def cmovgw1 : instruction :=
  definst "cmovgw" $ do
    pattern fun (v_2719 : reg (bv 16)) (v_2720 : reg (bv 16)) => do
      v_4392 <- getRegister zf;
      v_4394 <- getRegister sf;
      v_4395 <- getRegister of;
      v_4398 <- getRegister v_2719;
      v_4399 <- getRegister v_2720;
      setRegister (lhs.of_reg v_2720) (mux (bit_and (notBool_ v_4392) (eq v_4394 v_4395)) v_4398 v_4399);
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2716 : reg (bv 16)) => do
      v_7821 <- getRegister zf;
      v_7823 <- getRegister sf;
      v_7824 <- getRegister of;
      v_7827 <- evaluateAddress v_2715;
      v_7828 <- load v_7827 2;
      v_7829 <- getRegister v_2716;
      setRegister (lhs.of_reg v_2716) (mux (bit_and (notBool_ v_7821) (eq v_7823 v_7824)) v_7828 v_7829);
      pure ()
    pat_end
