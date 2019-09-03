def cmovpw1 : instruction :=
  definst "cmovpw" $ do
    pattern fun (v_3217 : reg (bv 16)) (v_3218 : reg (bv 16)) => do
      v_5117 <- getRegister pf;
      v_5119 <- getRegister v_3217;
      v_5120 <- getRegister v_3218;
      setRegister (lhs.of_reg v_3218) (mux (eq v_5117 (expression.bv_nat 1 1)) v_5119 v_5120);
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3213 : reg (bv 16)) => do
      v_8594 <- getRegister pf;
      v_8596 <- evaluateAddress v_3214;
      v_8597 <- load v_8596 2;
      v_8598 <- getRegister v_3213;
      setRegister (lhs.of_reg v_3213) (mux (eq v_8594 (expression.bv_nat 1 1)) v_8597 v_8598);
      pure ()
    pat_end
