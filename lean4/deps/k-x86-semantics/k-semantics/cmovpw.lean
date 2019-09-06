def cmovpw1 : instruction :=
  definst "cmovpw" $ do
    pattern fun (v_3307 : reg (bv 16)) (v_3308 : reg (bv 16)) => do
      v_5078 <- getRegister pf;
      v_5079 <- getRegister v_3307;
      v_5080 <- getRegister v_3308;
      setRegister (lhs.of_reg v_3308) (mux v_5078 v_5079 v_5080);
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3304 : reg (bv 16)) => do
      v_8303 <- getRegister pf;
      v_8304 <- evaluateAddress v_3303;
      v_8305 <- load v_8304 2;
      v_8306 <- getRegister v_3304;
      setRegister (lhs.of_reg v_3304) (mux v_8303 v_8305 v_8306);
      pure ()
    pat_end
