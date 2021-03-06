def imulq : instruction :=
  definst "imulq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 8;
      let v_5 <- eval (mul (sext v_4 128) (sext (handleImmediateWithSignExtend imm_0 32 32) 128));
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 128)));
      setRegister (lhs.of_reg r64_2) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- eval (mul (sext v_3 128) (sext (handleImmediateWithSignExtend imm_0 32 32) 128));
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 128)));
      setRegister (lhs.of_reg r64_2) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      let v_5 <- eval (mul (sext v_2 128) (sext v_4 128));
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 128)));
      setRegister (lhs.of_reg r64_1) v_6;
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
      let v_2 <- load v_1 8;
      let v_3 <- getRegister rax;
      let v_4 <- eval (mul (sext v_2 128) (sext v_3 128));
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 128)));
      let (v_7 : expression (bv 64)) <- eval (extract v_4 0 64);
      setRegister rax v_5;
      setRegister rdx v_7;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- eval (mul (sext v_2 128) (sext v_3 128));
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 128)));
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r64_0);
      let v_2 <- getRegister rax;
      let v_3 <- eval (mul (sext v_1 128) (sext v_2 128));
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- eval (notBool_ (eq v_3 (sext v_4 128)));
      let (v_6 : expression (bv 64)) <- eval (extract v_3 0 64);
      setRegister rax v_4;
      setRegister rdx v_6;
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
