def mull : instruction :=
  definst "mull" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 4;
      let v_3 <- eval (concat (expression.bv_nat 32 0) v_2);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_6 <- eval (concat (expression.bv_nat 32 0) v_5);
      let v_7 <- eval (mul v_3 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (notBool_ (eq v_8 (expression.bv_nat 32 0)));
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      setRegister eax v_10;
      setRegister edx v_8;
      setRegister af undef;
      setRegister cf v_9;
      setRegister of v_9;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      let v_2 <- eval (concat (expression.bv_nat 32 0) v_1);
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- eval (mul v_2 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (notBool_ (eq v_7 (expression.bv_nat 32 0)));
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      setRegister eax v_9;
      setRegister edx v_7;
      setRegister af undef;
      setRegister cf v_8;
      setRegister of v_8;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
