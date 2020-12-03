def sarl : instruction :=
  definst "sarl" $ do
    instr_pat $ fun (_ : clReg) (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 4;
      let v_3 <- eval (concat v_2 (expression.bv_nat 1 0));
      let v_4 <- getRegister rcx;
      let (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_6 <- eval (bv_and v_5 (expression.bv_nat 8 31));
      let v_7 <- eval (concat (expression.bv_nat 25 0) v_6);
      let v_8 <- eval (ashr v_3 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      store v_1 v_9 4;
      let v_11 <- eval (eq v_6 (expression.bv_nat 8 0));
      let v_12 <- getRegister zf;
      let v_13 <- getRegister sf;
      let v_14 <- getRegister pf;
      let (v_15 : expression (bv 8)) <- eval (extract v_8 24 32);
      let v_16 <- getRegister of;
      let v_17 <- getRegister cf;
      let v_18 <- getRegister af;
      setRegister af (mux v_11 v_18 undef);
      setRegister cf (mux v_11 v_17 (isBitSet v_8 32));
      setRegister of (bit_and (notBool_ (eq v_6 (expression.bv_nat 8 1))) (mux v_11 v_16 undef));
      setRegister pf (mux v_11 v_14 (parityFlag v_15));
      setRegister sf (mux v_11 v_13 (isBitSet v_8 0));
      setRegister zf (mux v_11 v_12 (eq v_9 (expression.bv_nat 32 0)));
      pure ()
     action;
    instr_pat $ fun (_ : clReg) (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rcx;
      let (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      let v_3 <- eval (bv_and v_2 (expression.bv_nat 8 31));
      let v_4 <- eval (eq v_3 (expression.bv_nat 8 0));
      let v_5 <- getRegister zf;
      let v_6 <- getRegister (lhs.of_reg r32_0);
      let v_7 <- eval (concat v_6 (expression.bv_nat 1 0));
      let v_8 <- eval (concat (expression.bv_nat 25 0) v_3);
      let v_9 <- eval (ashr v_7 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      let v_11 <- getRegister sf;
      let v_12 <- getRegister pf;
      let (v_13 : expression (bv 8)) <- eval (extract v_9 24 32);
      let v_14 <- getRegister of;
      let v_15 <- getRegister cf;
      let v_16 <- getRegister af;
      setRegister (lhs.of_reg r32_0) v_10;
      setRegister af (mux v_4 v_16 undef);
      setRegister cf (mux v_4 v_15 (isBitSet v_9 32));
      setRegister of (bit_and (notBool_ (eq v_3 (expression.bv_nat 8 1))) (mux v_4 v_14 undef));
      setRegister pf (mux v_4 v_12 (parityFlag v_13));
      setRegister sf (mux v_4 v_11 (isBitSet v_9 0));
      setRegister zf (mux v_4 v_5 (eq v_10 (expression.bv_nat 32 0)));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 4;
      let v_4 <- eval (concat v_3 (expression.bv_nat 1 0));
      let v_5 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      let v_6 <- eval (concat (expression.bv_nat 25 0) v_5);
      let v_7 <- eval (ashr v_4 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      store v_2 v_8 4;
      let v_10 <- eval (eq v_5 (expression.bv_nat 8 0));
      let v_11 <- getRegister zf;
      let v_12 <- getRegister sf;
      let v_13 <- getRegister pf;
      let (v_14 : expression (bv 8)) <- eval (extract v_7 24 32);
      let v_15 <- getRegister of;
      let v_16 <- getRegister cf;
      let v_17 <- getRegister af;
      setRegister af (mux v_10 v_17 undef);
      setRegister cf (mux v_10 v_16 (isBitSet v_7 32));
      setRegister of (bit_and (notBool_ (eq v_5 (expression.bv_nat 8 1))) (mux v_10 v_15 undef));
      setRegister pf (mux v_10 v_13 (parityFlag v_14));
      setRegister sf (mux v_10 v_12 (isBitSet v_7 0));
      setRegister zf (mux v_10 v_11 (eq v_8 (expression.bv_nat 32 0)));
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      let v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      let v_4 <- getRegister zf;
      let v_5 <- getRegister (lhs.of_reg r32_1);
      let v_6 <- eval (concat v_5 (expression.bv_nat 1 0));
      let v_7 <- eval (concat (expression.bv_nat 25 0) v_2);
      let v_8 <- eval (ashr v_6 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      let v_10 <- getRegister sf;
      let v_11 <- getRegister pf;
      let (v_12 : expression (bv 8)) <- eval (extract v_8 24 32);
      let v_13 <- getRegister of;
      let v_14 <- getRegister cf;
      let v_15 <- getRegister af;
      setRegister (lhs.of_reg r32_1) v_9;
      setRegister af (mux v_3 v_15 undef);
      setRegister cf (mux v_3 v_14 (isBitSet v_8 32));
      setRegister of (bit_and (notBool_ (eq v_2 (expression.bv_nat 8 1))) (mux v_3 v_13 undef));
      setRegister pf (mux v_3 v_11 (parityFlag v_12));
      setRegister sf (mux v_3 v_10 (isBitSet v_8 0));
      setRegister zf (mux v_3 v_4 (eq v_9 (expression.bv_nat 32 0)));
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 4;
      let v_3 <- eval (concat v_2 (expression.bv_nat 1 0));
      let v_4 <- eval (ashr v_3 (expression.bv_nat 33 1));
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      store v_1 v_5 4;
      let (v_7 : expression (bv 8)) <- eval (extract v_4 24 32);
      setRegister af undef;
      setRegister cf (isBitSet v_4 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      let v_2 <- eval (concat v_1 (expression.bv_nat 1 0));
      let v_3 <- eval (ashr v_2 (expression.bv_nat 33 1));
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 24 32);
      setRegister (lhs.of_reg r32_0) v_4;
      setRegister af undef;
      setRegister cf (isBitSet v_3 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action
