def cmovpow1 : instruction :=
  definst "cmovpow" $ do
    pattern fun (v_3289 : reg (bv 16)) (v_3290 : reg (bv 16)) => do
      v_5059 <- getRegister pf;
      v_5061 <- getRegister v_3289;
      v_5062 <- getRegister v_3290;
      setRegister (lhs.of_reg v_3290) (mux (notBool_ v_5059) v_5061 v_5062);
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3286 : reg (bv 16)) => do
      v_8290 <- getRegister pf;
      v_8292 <- evaluateAddress v_3285;
      v_8293 <- load v_8292 2;
      v_8294 <- getRegister v_3286;
      setRegister (lhs.of_reg v_3286) (mux (notBool_ v_8290) v_8293 v_8294);
      pure ()
    pat_end
