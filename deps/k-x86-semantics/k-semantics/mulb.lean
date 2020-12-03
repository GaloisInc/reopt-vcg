def mulb : instruction :=
  definst "mulb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 1;
      let v_3 <- eval (concat (expression.bv_nat 8 0) v_2);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_6 <- eval (concat (expression.bv_nat 8 0) v_5);
      let v_7 <- eval (mul v_3 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_7 0 8);
      let v_9 <- eval (notBool_ (eq v_8 (expression.bv_nat 8 0)));
      let (v_10 : expression (bv 48)) <- eval (extract v_4 0 48);
      let v_11 <- eval (concat v_10 v_7);
      setRegister rax v_11;
      setRegister af undef;
      setRegister cf v_9;
      setRegister of v_9;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg rh_0);
      let v_2 <- eval (concat (expression.bv_nat 8 0) v_1);
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_5 <- eval (concat (expression.bv_nat 8 0) v_4);
      let v_6 <- eval (mul v_2 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      let v_8 <- eval (notBool_ (eq v_7 (expression.bv_nat 8 0)));
      let (v_9 : expression (bv 48)) <- eval (extract v_3 0 48);
      let v_10 <- eval (concat v_9 v_6);
      setRegister rax v_10;
      setRegister af undef;
      setRegister cf v_8;
      setRegister of v_8;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
