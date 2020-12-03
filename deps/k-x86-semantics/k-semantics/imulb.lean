def imulb : instruction :=
  definst "imulb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 1;
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_5 <- eval (mul (sext v_2 16) (sext v_4 16));
      let (v_6 : expression (bv 8)) <- eval (extract v_5 8 16);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 16)));
      let (v_8 : expression (bv 48)) <- eval (extract v_3 0 48);
      let v_9 <- eval (concat v_8 v_5);
      setRegister rax v_9;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg rh_0);
      let v_2 <- getRegister rax;
      let (v_3 : expression (bv 8)) <- eval (extract v_2 56 64);
      let v_4 <- eval (mul (sext v_1 16) (sext v_3 16));
      let (v_5 : expression (bv 8)) <- eval (extract v_4 8 16);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 16)));
      let (v_7 : expression (bv 48)) <- eval (extract v_2 0 48);
      let v_8 <- eval (concat v_7 v_4);
      setRegister rax v_8;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
