def cmovngeq1 : instruction :=
  definst "cmovngeq" $ do
    pattern fun (v_2951 : reg (bv 64)) (v_2952 : reg (bv 64)) => do
      v_4752 <- getRegister sf;
      v_4754 <- getRegister of;
      v_4758 <- getRegister v_2951;
      v_4759 <- getRegister v_2952;
      setRegister (lhs.of_reg v_2952) (mux (notBool_ (eq (eq v_4752 (expression.bv_nat 1 1)) (eq v_4754 (expression.bv_nat 1 1)))) v_4758 v_4759);
      pure ()
    pat_end;
    pattern fun (v_2946 : Mem) (v_2947 : reg (bv 64)) => do
      v_8265 <- getRegister sf;
      v_8267 <- getRegister of;
      v_8271 <- evaluateAddress v_2946;
      v_8272 <- load v_8271 8;
      v_8273 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2947) (mux (notBool_ (eq (eq v_8265 (expression.bv_nat 1 1)) (eq v_8267 (expression.bv_nat 1 1)))) v_8272 v_8273);
      pure ()
    pat_end
