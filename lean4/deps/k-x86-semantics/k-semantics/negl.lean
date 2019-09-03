def negl1 : instruction :=
  definst "negl" $ do
    pattern fun (v_2842 : reg (bv 32)) => do
      v_4504 <- getRegister v_2842;
      v_4509 <- eval (add (expression.bv_nat 32 1) (bv_xor v_4504 (expression.bv_nat 32 4294967295)));
      v_4510 <- eval (extract v_4509 0 1);
      setRegister (lhs.of_reg v_2842) v_4509;
      setRegister of (mux (bit_and (eq (extract v_4504 0 1) (expression.bv_nat 1 1)) (eq v_4510 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4509 24 32));
      setRegister af (mux (notBool_ (eq (eq (extract v_4504 27 28) (expression.bv_nat 1 1)) (eq (extract v_4509 27 28) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4509);
      setRegister sf v_4510;
      setRegister cf (mux (notBool_ (eq v_4504 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2839 : Mem) => do
      v_11008 <- evaluateAddress v_2839;
      v_11009 <- load v_11008 4;
      v_11011 <- eval (add (expression.bv_nat 32 1) (bv_xor v_11009 (expression.bv_nat 32 4294967295)));
      store v_11008 v_11011 4;
      v_11016 <- eval (extract v_11011 0 1);
      setRegister of (mux (bit_and (eq (extract v_11009 0 1) (expression.bv_nat 1 1)) (eq v_11016 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11011 24 32));
      setRegister af (mux (notBool_ (eq (eq (extract v_11009 27 28) (expression.bv_nat 1 1)) (eq (extract v_11011 27 28) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11011);
      setRegister sf v_11016;
      setRegister cf (mux (notBool_ (eq v_11009 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
