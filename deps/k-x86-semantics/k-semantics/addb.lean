def addb : instruction :=
  definst "addb" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- load v_2 1;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      store v_2 v_8 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_3 <- eval (concat (expression.bv_nat 1 0) v_2);
      let v_4 <- getRegister (lhs.of_reg rh_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add v_3 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 1 9);
      setRegister (lhs.of_reg rh_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 3) (isBitSet v_6 4)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_2 v_4 v_7);
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- getRegister (lhs.of_reg rh_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      setRegister (lhs.of_reg rh_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg rh_0);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- load v_2 1;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      store v_2 v_8 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_3 v_5 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) v_2);
      let v_4 <- getRegister (lhs.of_reg rh_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add v_3 v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 1 9);
      setRegister (lhs.of_reg rh_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 3) (isBitSet v_6 4)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_2 v_4 v_7);
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
     action
