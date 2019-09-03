def cmovpq1 : instruction :=
  definst "cmovpq" $ do
    pattern fun (v_3220 : reg (bv 64)) (v_3221 : reg (bv 64)) => do
      v_5120 <- getRegister pf;
      v_5122 <- getRegister v_3220;
      v_5123 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3221) (mux (eq v_5120 (expression.bv_nat 1 1)) v_5122 v_5123);
      pure ()
    pat_end;
    pattern fun (v_3216 : Mem) (v_3217 : reg (bv 64)) => do
      v_8560 <- getRegister pf;
      v_8562 <- evaluateAddress v_3216;
      v_8563 <- load v_8562 8;
      v_8564 <- getRegister v_3217;
      setRegister (lhs.of_reg v_3217) (mux (eq v_8560 (expression.bv_nat 1 1)) v_8563 v_8564);
      pure ()
    pat_end
