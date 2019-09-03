def cmovngeq1 : instruction :=
  definst "cmovngeq" $ do
    pattern fun (v_2899 : reg (bv 64)) (v_2900 : reg (bv 64)) => do
      v_4701 <- getRegister sf;
      v_4703 <- getRegister of;
      v_4707 <- getRegister v_2899;
      v_4708 <- getRegister v_2900;
      setRegister (lhs.of_reg v_2900) (mux (notBool_ (eq (eq v_4701 (expression.bv_nat 1 1)) (eq v_4703 (expression.bv_nat 1 1)))) v_4707 v_4708);
      pure ()
    pat_end;
    pattern fun (v_2895 : Mem) (v_2896 : reg (bv 64)) => do
      v_8252 <- getRegister sf;
      v_8254 <- getRegister of;
      v_8258 <- evaluateAddress v_2895;
      v_8259 <- load v_8258 8;
      v_8260 <- getRegister v_2896;
      setRegister (lhs.of_reg v_2896) (mux (notBool_ (eq (eq v_8252 (expression.bv_nat 1 1)) (eq v_8254 (expression.bv_nat 1 1)))) v_8259 v_8260);
      pure ()
    pat_end
