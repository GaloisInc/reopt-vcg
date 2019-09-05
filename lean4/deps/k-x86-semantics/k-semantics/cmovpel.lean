def cmovpel1 : instruction :=
  definst "cmovpel" $ do
    pattern fun (v_3211 : reg (bv 32)) (v_3212 : reg (bv 32)) => do
      v_5098 <- getRegister pf;
      v_5100 <- getRegister v_3211;
      v_5101 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3212) (mux (eq v_5098 (expression.bv_nat 1 1)) v_5100 v_5101);
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3207 : reg (bv 32)) => do
      v_8521 <- getRegister pf;
      v_8523 <- evaluateAddress v_3204;
      v_8524 <- load v_8523 4;
      v_8525 <- getRegister v_3207;
      setRegister (lhs.of_reg v_3207) (mux (eq v_8521 (expression.bv_nat 1 1)) v_8524 v_8525);
      pure ()
    pat_end
