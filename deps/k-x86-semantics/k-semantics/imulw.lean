def imulw : instruction :=
  definst "imulw" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (r16_2 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 2;
      let v_5 <- eval (mul (sext v_4 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      setRegister (lhs.of_reg r16_2) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r16_1 : reg (bv 16)) (r16_2 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r16_1);
      let v_4 <- eval (mul (sext v_3 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      setRegister (lhs.of_reg r16_2) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 2;
      let v_5 <- eval (mul (sext v_2 32) (sext v_4 32));
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      setRegister (lhs.of_reg r16_1) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_5 <- eval (mul (sext v_2 32) (sext v_4 32));
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      let v_8 <- getRegister rdx;
      let (v_9 : expression (bv 48)) <- eval (extract v_8 0 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 48)) <- eval (extract v_3 0 48);
      let v_13 <- eval (concat v_12 v_6);
      setRegister rax v_13;
      setRegister rdx v_11;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_1);
      let v_3 <- getRegister (lhs.of_reg r16_0);
      let v_4 <- eval (mul (sext v_2 32) (sext v_3 32));
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      setRegister (lhs.of_reg r16_1) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r16_0);
      let v_2 <- getRegister rax;
      let (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      let v_4 <- eval (mul (sext v_1 32) (sext v_3 32));
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      let v_7 <- getRegister rdx;
      let (v_8 : expression (bv 48)) <- eval (extract v_7 0 48);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 48)) <- eval (extract v_2 0 48);
      let v_12 <- eval (concat v_11 v_5);
      setRegister rax v_12;
      setRegister rdx v_10;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
