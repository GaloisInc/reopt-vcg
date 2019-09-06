def cmovnpl1 : instruction :=
  definst "cmovnpl" $ do
    pattern fun (v_3106 : reg (bv 32)) (v_3107 : reg (bv 32)) => do
      v_4871 <- getRegister pf;
      v_4873 <- getRegister v_3106;
      v_4874 <- getRegister v_3107;
      setRegister (lhs.of_reg v_3107) (mux (notBool_ v_4871) v_4873 v_4874);
      pure ()
    pat_end;
    pattern fun (v_3099 : Mem) (v_3102 : reg (bv 32)) => do
      v_8168 <- getRegister pf;
      v_8170 <- evaluateAddress v_3099;
      v_8171 <- load v_8170 4;
      v_8172 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3102) (mux (notBool_ v_8168) v_8171 v_8172);
      pure ()
    pat_end
