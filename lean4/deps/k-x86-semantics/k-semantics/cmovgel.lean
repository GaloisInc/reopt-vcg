def cmovgel1 : instruction :=
  definst "cmovgel" $ do
    pattern fun (v_2568 : reg (bv 32)) (v_2569 : reg (bv 32)) => do
      v_4253 <- getRegister sf;
      v_4255 <- getRegister of;
      v_4258 <- getRegister v_2568;
      v_4259 <- getRegister v_2569;
      setRegister (lhs.of_reg v_2569) (mux (eq (eq v_4253 (expression.bv_nat 1 1)) (eq v_4255 (expression.bv_nat 1 1))) v_4258 v_4259);
      pure ()
    pat_end;
    pattern fun (v_2560 : Mem) (v_2561 : reg (bv 32)) => do
      v_7957 <- getRegister sf;
      v_7959 <- getRegister of;
      v_7962 <- evaluateAddress v_2560;
      v_7963 <- load v_7962 4;
      v_7964 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2561) (mux (eq (eq v_7957 (expression.bv_nat 1 1)) (eq v_7959 (expression.bv_nat 1 1))) v_7963 v_7964);
      pure ()
    pat_end
