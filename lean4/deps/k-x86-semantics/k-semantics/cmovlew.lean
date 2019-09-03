def cmovlew1 : instruction :=
  definst "cmovlew" $ do
    pattern fun (v_2680 : reg (bv 16)) (v_2681 : reg (bv 16)) => do
      v_4402 <- getRegister zf;
      v_4404 <- getRegister sf;
      v_4406 <- getRegister of;
      v_4411 <- getRegister v_2680;
      v_4412 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2681) (mux (bit_or (eq v_4402 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4404 (expression.bv_nat 1 1)) (eq v_4406 (expression.bv_nat 1 1))))) v_4411 v_4412);
      pure ()
    pat_end;
    pattern fun (v_2673 : Mem) (v_2672 : reg (bv 16)) => do
      v_8062 <- getRegister zf;
      v_8064 <- getRegister sf;
      v_8066 <- getRegister of;
      v_8071 <- evaluateAddress v_2673;
      v_8072 <- load v_8071 2;
      v_8073 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2672) (mux (bit_or (eq v_8062 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8064 (expression.bv_nat 1 1)) (eq v_8066 (expression.bv_nat 1 1))))) v_8072 v_8073);
      pure ()
    pat_end
