def addq : instruction :=
  definst "addq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_4 <- eval (sext v_3 64);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- load v_2 8;
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add v_5 v_7);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      store v_2 v_9 8;
      let (v_11 : expression (bv 8)) <- eval (extract v_8 57 65);
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_6 59))) (isBitSet v_8 60)));
      setRegister cf (isBitSet v_8 0);
      setRegister of (overflowFlag v_4 v_6 v_9);
      setRegister pf (parityFlag v_11);
      setRegister sf (isBitSet v_8 1);
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_3 <- eval (sext v_2 64);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r64_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      let (v_9 : expression (bv 8)) <- eval (extract v_7 57 65);
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_2 27) (isBitSet v_5 59))) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_9);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r64_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      let (v_9 : expression (bv 8)) <- eval (extract v_7 57 65);
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 59) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_9);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- load v_2 8;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      store v_2 v_8 8;
      let (v_10 : expression (bv 8)) <- eval (extract v_7 57 65);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 59) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_10);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) v_2);
      let v_4 <- getRegister (lhs.of_reg r64_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add v_3 v_5);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 1 65);
      let (v_8 : expression (bv 8)) <- eval (extract v_6 57 65);
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 59) (isBitSet v_6 60)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_2 v_4 v_7);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
     action
