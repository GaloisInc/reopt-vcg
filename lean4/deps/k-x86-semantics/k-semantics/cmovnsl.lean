def cmovnsl1 : instruction :=
  definst "cmovnsl" $ do
    pattern fun (v_3141 : reg (bv 32)) (v_3142 : reg (bv 32)) => do
      v_4906 <- getRegister sf;
      v_4908 <- getRegister v_3141;
      v_4909 <- getRegister v_3142;
      setRegister (lhs.of_reg v_3142) (mux (notBool_ v_4906) v_4908 v_4909);
      pure ()
    pat_end;
    pattern fun (v_3130 : Mem) (v_3133 : reg (bv 32)) => do
      v_8190 <- getRegister sf;
      v_8192 <- evaluateAddress v_3130;
      v_8193 <- load v_8192 4;
      v_8194 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3133) (mux (notBool_ v_8190) v_8193 v_8194);
      pure ()
    pat_end
