def btl : instruction :=
  definst "btl" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 5)) <- eval (extract v_3 0 5);
      let v_5 <- eval (concat (expression.bv_nat 59 0) (bv_and v_4 (expression.bv_nat 5 3)));
      let v_6 <- load (add v_2 v_5) 1;
      let (v_7 : expression (bv 3)) <- eval (extract v_3 5 8);
      let v_8 <- eval (concat (expression.bv_nat 5 0) (bv_and v_7 (expression.bv_nat 3 7)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6 v_8) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_1);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31)) 32)) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let (v_4 : expression (bv 61)) <- eval (extract (sext v_3 64) 0 61);
      let v_5 <- eval (concat (expression.bv_nat 3 0) v_4);
      let v_6 <- load (add v_2 v_5) 1;
      let (v_7 : expression (bv 3)) <- eval (extract v_3 29 32);
      let v_8 <- eval (concat (expression.bv_nat 5 0) v_7);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6 v_8) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_1);
      let v_3 <- getRegister (lhs.of_reg r32_0);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (bv_and v_3 (expression.bv_nat 32 31))) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
     action
