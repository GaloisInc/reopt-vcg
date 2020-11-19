def mulw : instruction :=
  definst "mulw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- getRegister rax;
      (v_4 : expression (bv 16)) <- eval (extract v_3 48 64);
      v_5 <- eval (mul (concat (expression.bv_nat 16 0) v_2) (concat (expression.bv_nat 16 0) v_4));
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      v_7 <- eval (notBool_ (eq v_6 (expression.bv_nat 16 0)));
      v_8 <- getRegister rdx;
      (v_9 : expression (bv 48)) <- eval (extract v_8 0 48);
      (v_10 : expression (bv 48)) <- eval (extract v_3 0 48);
      (v_11 : expression (bv 16)) <- eval (extract v_5 16 32);
      setRegister rax (concat v_10 v_11);
      setRegister rdx (concat v_9 v_6);
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister (lhs.of_reg r16_0);
      v_2 <- getRegister rax;
      (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      v_4 <- eval (mul (concat (expression.bv_nat 16 0) v_1) (concat (expression.bv_nat 16 0) v_3));
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- eval (notBool_ (eq v_5 (expression.bv_nat 16 0)));
      v_7 <- getRegister rdx;
      (v_8 : expression (bv 48)) <- eval (extract v_7 0 48);
      (v_9 : expression (bv 48)) <- eval (extract v_2 0 48);
      (v_10 : expression (bv 16)) <- eval (extract v_4 16 32);
      setRegister rax (concat v_9 v_10);
      setRegister rdx (concat v_8 v_5);
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
