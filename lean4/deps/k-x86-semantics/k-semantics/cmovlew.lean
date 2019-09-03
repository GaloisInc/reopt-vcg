def cmovlew1 : instruction :=
  definst "cmovlew" $ do
    pattern fun (v_2694 : reg (bv 16)) (v_2695 : reg (bv 16)) => do
      v_4415 <- getRegister zf;
      v_4417 <- getRegister sf;
      v_4419 <- getRegister of;
      v_4424 <- getRegister v_2694;
      v_4425 <- getRegister v_2695;
      setRegister (lhs.of_reg v_2695) (mux (bit_or (eq v_4415 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4417 (expression.bv_nat 1 1)) (eq v_4419 (expression.bv_nat 1 1))))) v_4424 v_4425);
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2686 : reg (bv 16)) => do
      v_8035 <- getRegister zf;
      v_8037 <- getRegister sf;
      v_8039 <- getRegister of;
      v_8044 <- evaluateAddress v_2684;
      v_8045 <- load v_8044 2;
      v_8046 <- getRegister v_2686;
      setRegister (lhs.of_reg v_2686) (mux (bit_or (eq v_8035 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8037 (expression.bv_nat 1 1)) (eq v_8039 (expression.bv_nat 1 1))))) v_8045 v_8046);
      pure ()
    pat_end
