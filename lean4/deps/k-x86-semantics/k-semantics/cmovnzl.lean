def cmovnzl1 : instruction :=
  definst "cmovnzl" $ do
    pattern fun (v_3157 : reg (bv 32)) (v_3158 : reg (bv 32)) => do
      v_5035 <- getRegister zf;
      v_5038 <- getRegister v_3157;
      v_5039 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3158) (mux (notBool_ (eq v_5035 (expression.bv_nat 1 1))) v_5038 v_5039);
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3153 : reg (bv 32)) => do
      v_8476 <- getRegister zf;
      v_8479 <- evaluateAddress v_3150;
      v_8480 <- load v_8479 4;
      v_8481 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3153) (mux (notBool_ (eq v_8476 (expression.bv_nat 1 1))) v_8480 v_8481);
      pure ()
    pat_end
