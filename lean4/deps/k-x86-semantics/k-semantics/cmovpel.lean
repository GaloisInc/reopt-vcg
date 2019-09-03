def cmovpel1 : instruction :=
  definst "cmovpel" $ do
    pattern fun (v_3157 : reg (bv 32)) (v_3158 : reg (bv 32)) => do
      v_5047 <- getRegister pf;
      v_5049 <- getRegister v_3157;
      v_5050 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3158) (mux (eq v_5047 (expression.bv_nat 1 1)) v_5049 v_5050);
      pure ()
    pat_end;
    pattern fun (v_3153 : Mem) (v_3154 : reg (bv 32)) => do
      v_8508 <- getRegister pf;
      v_8510 <- evaluateAddress v_3153;
      v_8511 <- load v_8510 4;
      v_8512 <- getRegister v_3154;
      setRegister (lhs.of_reg v_3154) (mux (eq v_8508 (expression.bv_nat 1 1)) v_8511 v_8512);
      pure ()
    pat_end
