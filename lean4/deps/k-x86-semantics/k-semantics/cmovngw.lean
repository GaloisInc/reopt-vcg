def cmovngw1 : instruction :=
  definst "cmovngw" $ do
    pattern fun (v_3013 : reg (bv 16)) (v_3014 : reg (bv 16)) => do
      v_4752 <- getRegister zf;
      v_4753 <- getRegister sf;
      v_4754 <- getRegister of;
      v_4758 <- getRegister v_3013;
      v_4759 <- getRegister v_3014;
      setRegister (lhs.of_reg v_3014) (mux (bit_or v_4752 (notBool_ (eq v_4753 v_4754))) v_4758 v_4759);
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) (v_3010 : reg (bv 16)) => do
      v_8079 <- getRegister zf;
      v_8080 <- getRegister sf;
      v_8081 <- getRegister of;
      v_8085 <- evaluateAddress v_3009;
      v_8086 <- load v_8085 2;
      v_8087 <- getRegister v_3010;
      setRegister (lhs.of_reg v_3010) (mux (bit_or v_8079 (notBool_ (eq v_8080 v_8081))) v_8086 v_8087);
      pure ()
    pat_end
