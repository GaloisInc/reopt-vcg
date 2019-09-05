def cmovnlw1 : instruction :=
  definst "cmovnlw" $ do
    pattern fun (v_3041 : reg (bv 16)) (v_3042 : reg (bv 16)) => do
      v_4908 <- getRegister sf;
      v_4910 <- getRegister of;
      v_4913 <- getRegister v_3041;
      v_4914 <- getRegister v_3042;
      setRegister (lhs.of_reg v_3042) (mux (eq (eq v_4908 (expression.bv_nat 1 1)) (eq v_4910 (expression.bv_nat 1 1))) v_4913 v_4914);
      pure ()
    pat_end;
    pattern fun (v_3036 : Mem) (v_3037 : reg (bv 16)) => do
      v_8391 <- getRegister sf;
      v_8393 <- getRegister of;
      v_8396 <- evaluateAddress v_3036;
      v_8397 <- load v_8396 2;
      v_8398 <- getRegister v_3037;
      setRegister (lhs.of_reg v_3037) (mux (eq (eq v_8391 (expression.bv_nat 1 1)) (eq v_8393 (expression.bv_nat 1 1))) v_8397 v_8398);
      pure ()
    pat_end
