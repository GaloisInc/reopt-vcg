def cmovpew1 : instruction :=
  definst "cmovpew" $ do
    pattern fun (v_3177 : reg (bv 16)) (v_3178 : reg (bv 16)) => do
      v_5067 <- getRegister pf;
      v_5069 <- getRegister v_3177;
      v_5070 <- getRegister v_3178;
      setRegister (lhs.of_reg v_3178) (mux (eq v_5067 (expression.bv_nat 1 1)) v_5069 v_5070);
      pure ()
    pat_end;
    pattern fun (v_3171 : Mem) (v_3173 : reg (bv 16)) => do
      v_8522 <- getRegister pf;
      v_8524 <- evaluateAddress v_3171;
      v_8525 <- load v_8524 2;
      v_8526 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3173) (mux (eq v_8522 (expression.bv_nat 1 1)) v_8525 v_8526);
      pure ()
    pat_end
