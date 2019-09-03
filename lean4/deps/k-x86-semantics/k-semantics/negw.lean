def negw1 : instruction :=
  definst "negw" $ do
    pattern fun (v_2856 : reg (bv 16)) => do
      v_4568 <- getRegister v_2856;
      v_4573 <- eval (add (expression.bv_nat 16 1) (bv_xor v_4568 (expression.bv_nat 16 65535)));
      v_4574 <- eval (extract v_4573 0 1);
      setRegister (lhs.of_reg v_2856) v_4573;
      setRegister of (mux (bit_and (eq (extract v_4568 0 1) (expression.bv_nat 1 1)) (eq v_4574 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4573 8 16));
      setRegister zf (zeroFlag v_4573);
      setRegister af (mux (notBool_ (eq (eq (extract v_4568 11 12) (expression.bv_nat 1 1)) (eq (extract v_4573 11 12) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4574;
      setRegister cf (mux (notBool_ (eq v_4568 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2853 : Mem) => do
      v_11068 <- evaluateAddress v_2853;
      v_11069 <- load v_11068 2;
      v_11071 <- eval (add (expression.bv_nat 16 1) (bv_xor v_11069 (expression.bv_nat 16 65535)));
      store v_11068 v_11071 2;
      v_11076 <- eval (extract v_11071 0 1);
      setRegister of (mux (bit_and (eq (extract v_11069 0 1) (expression.bv_nat 1 1)) (eq v_11076 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11071 8 16));
      setRegister af (mux (notBool_ (eq (eq (extract v_11069 11 12) (expression.bv_nat 1 1)) (eq (extract v_11071 11 12) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11071);
      setRegister sf v_11076;
      setRegister cf (mux (notBool_ (eq v_11069 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
