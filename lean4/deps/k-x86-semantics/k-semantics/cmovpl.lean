def cmovpl1 : instruction :=
  definst "cmovpl" $ do
    pattern fun (v_3265 : reg (bv 32)) (v_3266 : reg (bv 32)) => do
      v_5030 <- getRegister pf;
      v_5031 <- getRegister v_3265;
      v_5032 <- getRegister v_3266;
      setRegister (lhs.of_reg v_3266) (mux v_5030 v_5031 v_5032);
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3261 : reg (bv 32)) => do
      v_8270 <- getRegister pf;
      v_8271 <- evaluateAddress v_3258;
      v_8272 <- load v_8271 4;
      v_8273 <- getRegister v_3261;
      setRegister (lhs.of_reg v_3261) (mux v_8270 v_8272 v_8273);
      pure ()
    pat_end
