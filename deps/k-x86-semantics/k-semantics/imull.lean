def imull : instruction :=
  definst "imull" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 4;
      let v_5 <- eval (mul (sext v_4 64) (sext (handleImmediateWithSignExtend imm_0 32 32) 64));
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 64)));
      setRegister (lhs.of_reg r32_2) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- eval (mul (sext v_3 64) (sext (handleImmediateWithSignExtend imm_0 32 32) 64));
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 64)));
      setRegister (lhs.of_reg r32_2) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 4;
      let v_5 <- eval (mul (sext v_2 64) (sext v_4 64));
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 64)));
      setRegister (lhs.of_reg r32_1) v_6;
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
      let v_2 <- load v_1 4;
      let v_3 <- getRegister rax;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (mul (sext v_2 64) (sext v_4 64));
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (notBool_ (eq v_5 (sext v_6 64)));
      let (v_8 : expression (bv 32)) <- eval (extract v_5 0 32);
      setRegister eax v_6;
      setRegister edx v_8;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_1);
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let v_4 <- eval (mul (sext v_2 64) (sext v_3 64));
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 64)));
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      let v_2 <- getRegister rax;
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- eval (mul (sext v_1 64) (sext v_3 64));
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_6 <- eval (notBool_ (eq v_4 (sext v_5 64)));
      let (v_7 : expression (bv 32)) <- eval (extract v_4 0 32);
      setRegister eax v_5;
      setRegister edx v_7;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
     action
