def negq1 : instruction :=
  definst "negq" $ do
    pattern fun (v_2849 : reg (bv 64)) => do
      v_4536 <- getRegister v_2849;
      v_4541 <- eval (add (expression.bv_nat 64 1) (bv_xor v_4536 (expression.bv_nat 64 18446744073709551615)));
      v_4542 <- eval (extract v_4541 0 1);
      setRegister (lhs.of_reg v_2849) v_4541;
      setRegister of (mux (bit_and (eq (extract v_4536 0 1) (expression.bv_nat 1 1)) (eq v_4542 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4541 56 64));
      setRegister zf (zeroFlag v_4541);
      setRegister af (mux (notBool_ (eq (eq (extract v_4536 59 60) (expression.bv_nat 1 1)) (eq (extract v_4541 59 60) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4542;
      setRegister cf (mux (notBool_ (eq v_4536 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) => do
      v_11038 <- evaluateAddress v_2846;
      v_11039 <- load v_11038 8;
      v_11041 <- eval (add (expression.bv_nat 64 1) (bv_xor v_11039 (expression.bv_nat 64 18446744073709551615)));
      store v_11038 v_11041 8;
      v_11046 <- eval (extract v_11041 0 1);
      setRegister of (mux (bit_and (eq (extract v_11039 0 1) (expression.bv_nat 1 1)) (eq v_11046 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11041 56 64));
      setRegister af (mux (notBool_ (eq (eq (extract v_11039 59 60) (expression.bv_nat 1 1)) (eq (extract v_11041 59 60) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11041);
      setRegister sf v_11046;
      setRegister cf (mux (notBool_ (eq v_11039 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
