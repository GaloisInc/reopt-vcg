def cmovnzw1 : instruction :=
  definst "cmovnzw" $ do
    pattern fun (v_3173 : reg (bv 16)) (v_3174 : reg (bv 16)) => do
      v_5057 <- getRegister zf;
      v_5060 <- getRegister v_3173;
      v_5061 <- getRegister v_3174;
      setRegister (lhs.of_reg v_3174) (mux (notBool_ (eq v_5057 (expression.bv_nat 1 1))) v_5060 v_5061);
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3169 : reg (bv 16)) => do
      v_8492 <- getRegister zf;
      v_8495 <- evaluateAddress v_3168;
      v_8496 <- load v_8495 2;
      v_8497 <- getRegister v_3169;
      setRegister (lhs.of_reg v_3169) (mux (notBool_ (eq v_8492 (expression.bv_nat 1 1))) v_8496 v_8497);
      pure ()
    pat_end
