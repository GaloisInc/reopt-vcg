def cmovpq1 : instruction :=
  definst "cmovpq" $ do
    pattern fun (v_3209 : reg (bv 64)) (v_3210 : reg (bv 64)) => do
      v_5107 <- getRegister pf;
      v_5109 <- getRegister v_3209;
      v_5110 <- getRegister v_3210;
      setRegister (lhs.of_reg v_3210) (mux (eq v_5107 (expression.bv_nat 1 1)) v_5109 v_5110);
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3205 : reg (bv 64)) => do
      v_8587 <- getRegister pf;
      v_8589 <- evaluateAddress v_3204;
      v_8590 <- load v_8589 8;
      v_8591 <- getRegister v_3205;
      setRegister (lhs.of_reg v_3205) (mux (eq v_8587 (expression.bv_nat 1 1)) v_8590 v_8591);
      pure ()
    pat_end
