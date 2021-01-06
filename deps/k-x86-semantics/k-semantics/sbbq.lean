def sbbq : instruction :=
  definst "sbbq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_5 <- eval (sext v_4 64);
      let v_6 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_5 (expression.bv_nat 64 18446744073709551615)));
      let v_7 <- load v_2 8;
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let v_9 <- eval (add (mux v_3 v_6 (add v_6 (expression.bv_nat 65 1))) v_8);
      let (v_10 : expression (bv 64)) <- eval (extract v_9 1 65);
      store v_2 v_10 8;
      let v_12 <- eval (isBitSet v_9 1);
      let (v_13 : expression (bv 8)) <- eval (extract v_9 57 65);
      let (v_14 : expression (bv 1)) <- eval (extract v_5 0 1);
      let v_15 <- eval (eq (bv_xor v_14 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4 27) (isBitSet v_7 59))) (isBitSet v_9 60)));
      setRegister cf (isBitClear v_9 0);
      setRegister of (bit_and (eq v_15 (isBitSet v_7 0)) (notBool_ (eq v_15 v_12)));
      setRegister pf (parityFlag v_13);
      setRegister sf v_12;
      setRegister zf (zeroFlag v_10);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_4 <- eval (sext v_3 64);
      let v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      let v_6 <- getRegister (lhs.of_reg r64_1);
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_2 v_5 (add v_5 (expression.bv_nat 65 1))) v_7);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      let v_10 <- eval (isBitSet v_8 1);
      let (v_11 : expression (bv 8)) <- eval (extract v_8 57 65);
      let (v_12 : expression (bv 1)) <- eval (extract v_4 0 1);
      let v_13 <- eval (eq (bv_xor v_12 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_9;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_6 59))) (isBitSet v_8 60)));
      setRegister cf (isBitClear v_8 0);
      setRegister of (bit_and (eq v_13 (isBitSet v_6 0)) (notBool_ (eq v_13 v_10)));
      setRegister pf (parityFlag v_11);
      setRegister sf v_10;
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      let v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      let v_6 <- getRegister (lhs.of_reg r64_1);
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_2 v_5 (add v_5 (expression.bv_nat 65 1))) v_7);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      let v_10 <- eval (isBitSet v_8 1);
      let (v_11 : expression (bv 8)) <- eval (extract v_8 57 65);
      let (v_12 : expression (bv 1)) <- eval (extract v_4 0 1);
      let v_13 <- eval (eq (bv_xor v_12 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_9;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_8 60)));
      setRegister cf (isBitClear v_8 0);
      setRegister of (bit_and (eq v_13 (isBitSet v_6 0)) (notBool_ (eq v_13 v_10)));
      setRegister pf (parityFlag v_11);
      setRegister sf v_10;
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister cf;
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      let v_6 <- load v_2 8;
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (add (mux v_3 v_5 (add v_5 (expression.bv_nat 65 1))) v_7);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      store v_2 v_9 8;
      let v_11 <- eval (isBitSet v_8 1);
      let (v_12 : expression (bv 8)) <- eval (extract v_8 57 65);
      let (v_13 : expression (bv 1)) <- eval (extract v_4 0 1);
      let v_14 <- eval (eq (bv_xor v_13 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_8 60)));
      setRegister cf (isBitClear v_8 0);
      setRegister of (bit_and (eq v_14 (isBitSet v_6 0)) (notBool_ (eq v_14 v_11)));
      setRegister pf (parityFlag v_12);
      setRegister sf v_11;
      setRegister zf (zeroFlag v_9);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615)));
      let v_5 <- getRegister (lhs.of_reg r64_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (add (mux v_2 v_4 (add v_4 (expression.bv_nat 65 1))) v_6);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      let v_9 <- eval (isBitSet v_7 1);
      let (v_10 : expression (bv 8)) <- eval (extract v_7 57 65);
      let (v_11 : expression (bv 1)) <- eval (extract v_3 0 1);
      let v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 59) (isBitSet v_7 60)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
     action
