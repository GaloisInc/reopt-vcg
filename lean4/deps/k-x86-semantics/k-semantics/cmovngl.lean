def cmovngl1 : instruction :=
  definst "cmovngl" $ do
    pattern fun (v_2998 : reg (bv 32)) (v_2999 : reg (bv 32)) => do
      v_4724 <- getRegister zf;
      v_4725 <- getRegister sf;
      v_4726 <- getRegister of;
      v_4730 <- getRegister v_2998;
      v_4731 <- getRegister v_2999;
      setRegister (lhs.of_reg v_2999) (mux (bit_or v_4724 (notBool_ (eq v_4725 v_4726))) v_4730 v_4731);
      pure ()
    pat_end;
    pattern fun (v_2991 : Mem) (v_2994 : reg (bv 32)) => do
      v_8057 <- getRegister zf;
      v_8058 <- getRegister sf;
      v_8059 <- getRegister of;
      v_8063 <- evaluateAddress v_2991;
      v_8064 <- load v_8063 4;
      v_8065 <- getRegister v_2994;
      setRegister (lhs.of_reg v_2994) (mux (bit_or v_8057 (notBool_ (eq v_8058 v_8059))) v_8064 v_8065);
      pure ()
    pat_end
