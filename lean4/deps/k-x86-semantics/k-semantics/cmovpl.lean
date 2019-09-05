def cmovpl1 : instruction :=
  definst "cmovpl" $ do
    pattern fun (v_3238 : reg (bv 32)) (v_3239 : reg (bv 32)) => do
      v_5128 <- getRegister pf;
      v_5130 <- getRegister v_3238;
      v_5131 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3239) (mux (eq v_5128 (expression.bv_nat 1 1)) v_5130 v_5131);
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3234 : reg (bv 32)) => do
      v_8542 <- getRegister pf;
      v_8544 <- evaluateAddress v_3231;
      v_8545 <- load v_8544 4;
      v_8546 <- getRegister v_3234;
      setRegister (lhs.of_reg v_3234) (mux (eq v_8542 (expression.bv_nat 1 1)) v_8545 v_8546);
      pure ()
    pat_end
