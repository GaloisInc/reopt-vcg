def salw : instruction :=
  definst "salw" $ do
    instr_pat $ fun (_ : clReg) (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      let v_3 <- eval (concat (expression.bv_nat 1 0) v_2);
      let v_4 <- getRegister rcx;
      let (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_6 <- eval (bv_and v_5 (expression.bv_nat 8 31));
      let v_7 <- eval (concat (expression.bv_nat 9 0) v_6);
      let (v_8 : expression (bv 17)) <- eval (extract (shl v_3 v_7) 0 17);
      let (v_9 : expression (bv 16)) <- eval (extract v_8 1 17);
      store v_1 v_9 2;
      let v_11 <- eval (eq v_6 (expression.bv_nat 8 0));
      let v_12 <- getRegister zf;
      let v_13 <- getRegister sf;
      let v_14 <- eval (isBitSet v_8 1);
      let v_15 <- getRegister pf;
      let (v_16 : expression (bv 8)) <- eval (extract v_8 9 17);
      let v_17 <- getRegister cf;
      let v_18 <- eval (mux (uge v_6 (expression.bv_nat 8 16)) undef (mux v_11 v_17 (isBitSet v_8 0)));
      let v_19 <- getRegister of;
      let v_20 <- getRegister af;
      setRegister af (mux v_11 v_20 undef);
      setRegister cf v_18;
      setRegister of (mux (eq v_6 (expression.bv_nat 8 1)) (notBool_ (eq v_18 v_14)) (mux v_11 v_19 undef));
      setRegister pf (mux v_11 v_15 (parityFlag v_16));
      setRegister sf (mux v_11 v_13 v_14);
      setRegister zf (mux v_11 v_12 (eq v_9 (expression.bv_nat 16 0)));
      pure ()
     action;
    instr_pat $ fun (_ : clReg) (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rcx;
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let v_3 <- eval (bv_and v_2 (expression.bv_nat 8 31));
      let v_4 <- eval (eq v_3 (expression.bv_nat 8 0));
      let v_5 <- getRegister zf;
      let v_6 <- getRegister (lhs.of_reg r16_0);
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (concat (expression.bv_nat 9 0) v_3);
      let (v_9 : expression (bv 17)) <- eval (extract (shl v_7 v_8) 0 17);
      let (v_10 : expression (bv 16)) <- eval (extract v_9 1 17);
      let v_11 <- getRegister sf;
      let v_12 <- eval (isBitSet v_9 1);
      let v_13 <- getRegister pf;
      let (v_14 : expression (bv 8)) <- eval (extract v_9 9 17);
      let v_15 <- getRegister cf;
      let v_16 <- eval (mux (uge v_3 (expression.bv_nat 8 16)) undef (mux v_4 v_15 (isBitSet v_9 0)));
      let v_17 <- getRegister of;
      let v_18 <- getRegister af;
      setRegister (lhs.of_reg r16_0) v_10;
      setRegister af (mux v_4 v_18 undef);
      setRegister cf v_16;
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq v_16 v_12)) (mux v_4 v_17 undef));
      setRegister pf (mux v_4 v_13 (parityFlag v_14));
      setRegister sf (mux v_4 v_11 v_12);
      setRegister zf (mux v_4 v_5 (eq v_10 (expression.bv_nat 16 0)));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 2;
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let v_5 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      let v_6 <- eval (concat (expression.bv_nat 9 0) v_5);
      let (v_7 : expression (bv 17)) <- eval (extract (shl v_4 v_6) 0 17);
      let (v_8 : expression (bv 16)) <- eval (extract v_7 1 17);
      store v_2 v_8 2;
      let v_10 <- eval (eq v_5 (expression.bv_nat 8 0));
      let v_11 <- getRegister zf;
      let v_12 <- getRegister sf;
      let v_13 <- eval (isBitSet v_7 1);
      let v_14 <- getRegister pf;
      let (v_15 : expression (bv 8)) <- eval (extract v_7 9 17);
      let v_16 <- getRegister cf;
      let v_17 <- eval (mux (uge v_5 (expression.bv_nat 8 16)) undef (mux v_10 v_16 (isBitSet v_7 0)));
      let v_18 <- getRegister of;
      let v_19 <- getRegister af;
      setRegister af (mux v_10 v_19 undef);
      setRegister cf v_17;
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq v_17 v_13)) (mux v_10 v_18 undef));
      setRegister pf (mux v_10 v_14 (parityFlag v_15));
      setRegister sf (mux v_10 v_12 v_13);
      setRegister zf (mux v_10 v_11 (eq v_8 (expression.bv_nat 16 0)));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      let v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      let v_4 <- getRegister zf;
      let v_5 <- getRegister (lhs.of_reg r16_1);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 9 0) v_2);
      let (v_8 : expression (bv 17)) <- eval (extract (shl v_6 v_7) 0 17);
      let (v_9 : expression (bv 16)) <- eval (extract v_8 1 17);
      let v_10 <- getRegister sf;
      let v_11 <- eval (isBitSet v_8 1);
      let v_12 <- getRegister pf;
      let (v_13 : expression (bv 8)) <- eval (extract v_8 9 17);
      let v_14 <- getRegister cf;
      let v_15 <- eval (mux (uge v_2 (expression.bv_nat 8 16)) undef (mux v_3 v_14 (isBitSet v_8 0)));
      let v_16 <- getRegister of;
      let v_17 <- getRegister af;
      setRegister (lhs.of_reg r16_1) v_9;
      setRegister af (mux v_3 v_17 undef);
      setRegister cf v_15;
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_15 v_11)) (mux v_3 v_16 undef));
      setRegister pf (mux v_3 v_12 (parityFlag v_13));
      setRegister sf (mux v_3 v_10 v_11);
      setRegister zf (mux v_3 v_4 (eq v_9 (expression.bv_nat 16 0)));
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      let v_3 <- eval (concat (expression.bv_nat 1 0) v_2);
      let (v_4 : expression (bv 17)) <- eval (extract (shl v_3 (expression.bv_nat 17 1)) 0 17);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 1 17);
      store v_1 v_5 2;
      let v_7 <- eval (isBitSet v_4 1);
      let (v_8 : expression (bv 8)) <- eval (extract v_4 9 17);
      let v_9 <- eval (isBitSet v_4 0);
      setRegister af undef;
      setRegister cf v_9;
      setRegister of (notBool_ (eq v_9 v_7));
      setRegister pf (parityFlag v_8);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r16_0);
      let v_2 <- eval (concat (expression.bv_nat 1 0) v_1);
      let (v_3 : expression (bv 17)) <- eval (extract (shl v_2 (expression.bv_nat 17 1)) 0 17);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 1 17);
      let v_5 <- eval (isBitSet v_3 1);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 9 17);
      let v_7 <- eval (isBitSet v_3 0);
      setRegister (lhs.of_reg r16_0) v_4;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of (notBool_ (eq v_7 v_5));
      setRegister pf (parityFlag v_6);
      setRegister sf v_5;
      setRegister zf (zeroFlag v_4);
      pure ()
     action
