def cmovnoq1 : instruction :=
  definst "cmovnoq" $ do
    pattern fun (v_3007 : reg (bv 64)) (v_3008 : reg (bv 64)) => do
      v_4881 <- getRegister of;
      v_4884 <- getRegister v_3007;
      v_4885 <- getRegister v_3008;
      setRegister (lhs.of_reg v_3008) (mux (notBool_ (eq v_4881 (expression.bv_nat 1 1))) v_4884 v_4885);
      pure ()
    pat_end;
    pattern fun (v_3003 : Mem) (v_3004 : reg (bv 64)) => do
      v_8396 <- getRegister of;
      v_8399 <- evaluateAddress v_3003;
      v_8400 <- load v_8399 8;
      v_8401 <- getRegister v_3004;
      setRegister (lhs.of_reg v_3004) (mux (notBool_ (eq v_8396 (expression.bv_nat 1 1))) v_8400 v_8401);
      pure ()
    pat_end
