def cmovnlew1 : instruction :=
  definst "cmovnlew" $ do
    pattern fun (v_3040 : reg (bv 16)) (v_3041 : reg (bv 16)) => do
      v_4794 <- getRegister zf;
      v_4796 <- getRegister sf;
      v_4797 <- getRegister of;
      v_4800 <- getRegister v_3040;
      v_4801 <- getRegister v_3041;
      setRegister (lhs.of_reg v_3041) (mux (bit_and (notBool_ v_4794) (eq v_4796 v_4797)) v_4800 v_4801);
      pure ()
    pat_end;
    pattern fun (v_3036 : Mem) (v_3037 : reg (bv 16)) => do
      v_8112 <- getRegister zf;
      v_8114 <- getRegister sf;
      v_8115 <- getRegister of;
      v_8118 <- evaluateAddress v_3036;
      v_8119 <- load v_8118 2;
      v_8120 <- getRegister v_3037;
      setRegister (lhs.of_reg v_3037) (mux (bit_and (notBool_ v_8112) (eq v_8114 v_8115)) v_8119 v_8120);
      pure ()
    pat_end
