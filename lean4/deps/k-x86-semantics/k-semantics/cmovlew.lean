def cmovlew1 : instruction :=
  definst "cmovlew" $ do
    pattern fun (v_2770 : reg (bv 16)) (v_2771 : reg (bv 16)) => do
      v_4449 <- getRegister zf;
      v_4450 <- getRegister sf;
      v_4451 <- getRegister of;
      v_4455 <- getRegister v_2770;
      v_4456 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2771) (mux (bit_or v_4449 (notBool_ (eq v_4450 v_4451))) v_4455 v_4456);
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) (v_2763 : reg (bv 16)) => do
      v_7857 <- getRegister zf;
      v_7858 <- getRegister sf;
      v_7859 <- getRegister of;
      v_7863 <- evaluateAddress v_2762;
      v_7864 <- load v_7863 2;
      v_7865 <- getRegister v_2763;
      setRegister (lhs.of_reg v_2763) (mux (bit_or v_7857 (notBool_ (eq v_7858 v_7859))) v_7864 v_7865);
      pure ()
    pat_end
