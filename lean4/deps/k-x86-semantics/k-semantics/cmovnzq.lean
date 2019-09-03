def cmovnzq1 : instruction :=
  definst "cmovnzq" $ do
    pattern fun (v_3112 : reg (bv 64)) (v_3113 : reg (bv 64)) => do
      v_4995 <- getRegister zf;
      v_4998 <- getRegister v_3112;
      v_4999 <- getRegister v_3113;
      setRegister (lhs.of_reg v_3113) (mux (notBool_ (eq v_4995 (expression.bv_nat 1 1))) v_4998 v_4999);
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 64)) => do
      v_8471 <- getRegister zf;
      v_8474 <- evaluateAddress v_3108;
      v_8475 <- load v_8474 8;
      v_8476 <- getRegister v_3109;
      setRegister (lhs.of_reg v_3109) (mux (notBool_ (eq v_8471 (expression.bv_nat 1 1))) v_8475 v_8476);
      pure ()
    pat_end
