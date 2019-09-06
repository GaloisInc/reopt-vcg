def cmovnol1 : instruction :=
  definst "cmovnol" $ do
    pattern fun (v_3079 : reg (bv 32)) (v_3080 : reg (bv 32)) => do
      v_4841 <- getRegister of;
      v_4843 <- getRegister v_3079;
      v_4844 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3080) (mux (notBool_ v_4841) v_4843 v_4844);
      pure ()
    pat_end;
    pattern fun (v_3072 : Mem) (v_3075 : reg (bv 32)) => do
      v_8147 <- getRegister of;
      v_8149 <- evaluateAddress v_3072;
      v_8150 <- load v_8149 4;
      v_8151 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3075) (mux (notBool_ v_8147) v_8150 v_8151);
      pure ()
    pat_end
