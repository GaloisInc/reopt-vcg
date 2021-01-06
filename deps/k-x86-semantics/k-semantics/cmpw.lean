def cmpw : instruction :=
  definst "cmpw" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535)));
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 2;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_3 (expression.bv_nat 17 1)) v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_7 1 17);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 9 17);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_5) 11) (isBitSet v_7 12)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535)));
      let v_4 <- getRegister (lhs.of_reg r16_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add (add v_3 (expression.bv_nat 17 1)) v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 1 17);
      let v_8 <- eval (isBitSet v_6 1);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 9 17);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 11) (isBitSet v_6 12)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_4 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_7);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let v_4 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 16 65535)));
      let v_5 <- getRegister (lhs.of_reg r16_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_4 (expression.bv_nat 17 1)) v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_7 1 17);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 9 17);
      let (v_11 : expression (bv 1)) <- eval (extract v_3 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 11) (isBitSet v_7 12)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535)));
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 2;
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (add v_3 (expression.bv_nat 17 1)) v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_7 1 17);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 9 17);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_5) 11) (isBitSet v_7 12)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_0);
      let v_3 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535)));
      let v_4 <- getRegister (lhs.of_reg r16_1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- eval (add (add v_3 (expression.bv_nat 17 1)) v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 1 17);
      let v_8 <- eval (isBitSet v_6 1);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 9 17);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 11) (isBitSet v_6 12)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_4 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_7);
      pure ()
     action
