def mulw : instruction :=
  definst "mulw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      let v_3 <- eval (concat (expression.bv_nat 16 0) v_2);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 48 64);
      let v_6 <- eval (concat (expression.bv_nat 16 0) v_5);
      let v_7 <- eval (mul v_3 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let v_9 <- eval (notBool_ (eq v_8 (expression.bv_nat 16 0)));
      let v_10 <- getRegister rdx;
      let (v_11 : expression (bv 48)) <- eval (extract v_10 0 48);
      let v_12 <- eval (concat v_11 v_8);
      let (v_13 : expression (bv 48)) <- eval (extract v_4 0 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_15 <- eval (concat v_13 v_14);
      setRegister rax v_15;
      setRegister rdx v_12;
      setRegister af undef;
      setRegister cf v_9;
      setRegister of v_9;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r16_0);
      let v_2 <- eval (concat (expression.bv_nat 16 0) v_1);
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_5 <- eval (concat (expression.bv_nat 16 0) v_4);
      let v_6 <- eval (mul v_2 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (notBool_ (eq v_7 (expression.bv_nat 16 0)));
      let v_9 <- getRegister rdx;
      let (v_10 : expression (bv 48)) <- eval (extract v_9 0 48);
      let v_11 <- eval (concat v_10 v_7);
      let (v_12 : expression (bv 48)) <- eval (extract v_3 0 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_14 <- eval (concat v_12 v_13);
      setRegister rax v_14;
      setRegister rdx v_11;
      setRegister af undef;
      setRegister cf v_8;
      setRegister of v_8;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
