def mulq : instruction :=
  definst "mulq" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 8;
      let v_3 <- eval (concat (expression.bv_nat 64 0) v_2);
      let v_4 <- getRegister rax;
      let v_5 <- eval (concat (expression.bv_nat 64 0) v_4);
      let v_6 <- eval (mul v_3 v_5);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let v_8 <- eval (notBool_ (eq v_7 (expression.bv_nat 64 0)));
      let (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      setRegister rax v_9;
      setRegister rdx v_7;
      setRegister af undef;
      setRegister cf v_8;
      setRegister of v_8;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r64_0);
      let v_2 <- eval (concat (expression.bv_nat 64 0) v_1);
      let v_3 <- getRegister rax;
      let v_4 <- eval (concat (expression.bv_nat 64 0) v_3);
      let v_5 <- eval (mul v_2 v_4);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- eval (notBool_ (eq v_6 (expression.bv_nat 64 0)));
      let (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister rax v_8;
      setRegister rdx v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
