def mulw1 : instruction :=
  definst "mulw" $ do
    pattern fun (v_2770 : reg (bv 16)) => do
      v_4268 <- getRegister v_2770;
      v_4270 <- getRegister rax;
      v_4273 <- eval (mul (concat (expression.bv_nat 16 0) v_4268) (concat (expression.bv_nat 16 0) (extract v_4270 48 64)));
      v_4274 <- eval (extract v_4273 0 16);
      v_4277 <- eval (mux (notBool_ (eq v_4274 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4281 <- getRegister rdx;
      setRegister rdx (concat (extract v_4281 0 48) v_4274);
      setRegister rax (concat (extract v_4270 0 48) (extract v_4273 16 32));
      setRegister of v_4277;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4277;
      pure ()
    pat_end;
    pattern fun (v_2766 : Mem) => do
      v_9044 <- evaluateAddress v_2766;
      v_9045 <- load v_9044 2;
      v_9047 <- getRegister rax;
      v_9050 <- eval (mul (concat (expression.bv_nat 16 0) v_9045) (concat (expression.bv_nat 16 0) (extract v_9047 48 64)));
      v_9051 <- eval (extract v_9050 0 16);
      v_9054 <- eval (mux (notBool_ (eq v_9051 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_9058 <- getRegister rdx;
      setRegister rdx (concat (extract v_9058 0 48) v_9051);
      setRegister rax (concat (extract v_9047 0 48) (extract v_9050 16 32));
      setRegister of v_9054;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9054;
      pure ()
    pat_end
