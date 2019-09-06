def cmovnew1 : instruction :=
  definst "cmovnew" $ do
    pattern fun (v_2959 : reg (bv 16)) (v_2960 : reg (bv 16)) => do
      v_4678 <- getRegister zf;
      v_4680 <- getRegister v_2959;
      v_4681 <- getRegister v_2960;
      setRegister (lhs.of_reg v_2960) (mux (notBool_ v_4678) v_4680 v_4681);
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 16)) => do
      v_8023 <- getRegister zf;
      v_8025 <- evaluateAddress v_2955;
      v_8026 <- load v_8025 2;
      v_8027 <- getRegister v_2956;
      setRegister (lhs.of_reg v_2956) (mux (notBool_ v_8023) v_8026 v_8027);
      pure ()
    pat_end
