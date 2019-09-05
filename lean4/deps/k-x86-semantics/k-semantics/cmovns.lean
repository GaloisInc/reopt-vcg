def cmovns1 : instruction :=
  definst "cmovns" $ do
    pattern fun (v_3099 : Mem) (v_3102 : reg (bv 32)) => do
      v_9045 <- getRegister sf;
      v_9048 <- evaluateAddress v_3099;
      v_9049 <- load v_9048 4;
      v_9050 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3102) (mux (notBool_ (eq v_9045 (expression.bv_nat 1 1))) v_9049 v_9050);
      pure ()
    pat_end;
    pattern fun (v_3117 : Mem) (v_3116 : reg (bv 64)) => do
      v_9053 <- getRegister sf;
      v_9056 <- evaluateAddress v_3117;
      v_9057 <- load v_9056 8;
      v_9058 <- getRegister v_3116;
      setRegister (lhs.of_reg v_3116) (mux (notBool_ (eq v_9053 (expression.bv_nat 1 1))) v_9057 v_9058);
      pure ()
    pat_end;
    pattern fun (v_3134 : Mem) (v_3133 : reg (bv 16)) => do
      v_9061 <- getRegister sf;
      v_9064 <- evaluateAddress v_3134;
      v_9065 <- load v_9064 2;
      v_9066 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3133) (mux (notBool_ (eq v_9061 (expression.bv_nat 1 1))) v_9065 v_9066);
      pure ()
    pat_end
