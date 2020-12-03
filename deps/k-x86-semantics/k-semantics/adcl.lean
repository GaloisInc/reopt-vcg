def adcl : instruction :=
  definst "adcl" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- load v_2 4;
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 33 1)) v_5) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 1 33);
      store v_2 v_9 4;
      let (v_11 : expression (bv 8)) <- eval (extract v_8 25 33);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_8 28)));
      setRegister cf (isBitSet v_8 0);
      setRegister of (overflowFlag v_4 v_6 v_9);
      setRegister pf (parityFlag v_11);
      setRegister sf (isBitSet v_8 1);
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r32_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 33 1)) v_4) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 1 33);
      let (v_9 : expression (bv 8)) <- eval (extract v_7 25 33);
      setRegister (lhs.of_reg r32_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 27) (isBitSet v_7 28)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_9);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 4;
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- getRegister (lhs.of_reg r32_1);
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_2 (add v_5 (expression.bv_nat 33 1)) v_5) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 1 33);
      let (v_10 : expression (bv 8)) <- eval (extract v_8 25 33);
      setRegister (lhs.of_reg r32_1) v_9;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_8 28)));
      setRegister cf (isBitSet v_8 0);
      setRegister of (overflowFlag v_4 v_6 v_9);
      setRegister pf (parityFlag v_10);
      setRegister sf (isBitSet v_8 1);
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- getRegister (lhs.of_reg r32_0);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- load v_2 4;
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 33 1)) v_5) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 1 33);
      store v_2 v_9 4;
      let (v_11 : expression (bv 8)) <- eval (extract v_8 25 33);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_8 28)));
      setRegister cf (isBitSet v_8 0);
      setRegister of (overflowFlag v_4 v_6 v_9);
      setRegister pf (parityFlag v_11);
      setRegister sf (isBitSet v_8 1);
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r32_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 33 1)) v_4) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 1 33);
      let (v_9 : expression (bv 8)) <- eval (extract v_7 25 33);
      setRegister (lhs.of_reg r32_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 27) (isBitSet v_7 28)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_9);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action
