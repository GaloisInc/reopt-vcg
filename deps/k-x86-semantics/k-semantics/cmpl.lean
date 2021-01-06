def cmpl : instruction :=
  definst "cmpl" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295)));
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 4;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_3 (expression.bv_nat 33 1)) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 1 33);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 25 33);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_5) 27) (isBitSet v_7 28)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295)));
      let v_4 <- getRegister (lhs.of_reg r32_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add (add v_3 (expression.bv_nat 33 1)) v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 1 33);
      let v_8 <- eval (isBitSet v_6 1);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 25 33);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 27) (isBitSet v_6 28)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_4 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_7);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let v_4 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 32 4294967295)));
      let v_5 <- getRegister (lhs.of_reg r32_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_4 (expression.bv_nat 33 1)) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 1 33);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 25 33);
      let (v_11 : expression (bv 1)) <- eval (extract v_3 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 27) (isBitSet v_7 28)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295)));
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 4;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_3 (expression.bv_nat 33 1)) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 1 33);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 25 33);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_5) 27) (isBitSet v_7 28)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295)));
      let v_4 <- getRegister (lhs.of_reg r32_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add (add v_3 (expression.bv_nat 33 1)) v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 1 33);
      let v_8 <- eval (isBitSet v_6 1);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 25 33);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 27) (isBitSet v_6 28)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_4 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_7);
      pure ()
     action
