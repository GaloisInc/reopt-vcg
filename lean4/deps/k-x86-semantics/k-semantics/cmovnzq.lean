def cmovnzq1 : instruction :=
  definst "cmovnzq" $ do
    pattern fun (v_3101 : reg (bv 64)) (v_3102 : reg (bv 64)) => do
      v_4982 <- getRegister zf;
      v_4985 <- getRegister v_3101;
      v_4986 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3102) (mux (notBool_ (eq v_4982 (expression.bv_nat 1 1))) v_4985 v_4986);
      pure ()
    pat_end;
    pattern fun (v_3096 : Mem) (v_3097 : reg (bv 64)) => do
      v_8498 <- getRegister zf;
      v_8501 <- evaluateAddress v_3096;
      v_8502 <- load v_8501 8;
      v_8503 <- getRegister v_3097;
      setRegister (lhs.of_reg v_3097) (mux (notBool_ (eq v_8498 (expression.bv_nat 1 1))) v_8502 v_8503);
      pure ()
    pat_end
