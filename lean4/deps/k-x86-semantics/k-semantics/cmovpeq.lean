def cmovpeq1 : instruction :=
  definst "cmovpeq" $ do
    pattern fun (v_3155 : reg (bv 64)) (v_3156 : reg (bv 64)) => do
      v_5044 <- getRegister pf;
      v_5046 <- getRegister v_3155;
      v_5047 <- getRegister v_3156;
      setRegister (lhs.of_reg v_3156) (mux (eq v_5044 (expression.bv_nat 1 1)) v_5046 v_5047);
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3151 : reg (bv 64)) => do
      v_8542 <- getRegister pf;
      v_8544 <- evaluateAddress v_3150;
      v_8545 <- load v_8544 8;
      v_8546 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3151) (mux (eq v_8542 (expression.bv_nat 1 1)) v_8545 v_8546);
      pure ()
    pat_end
