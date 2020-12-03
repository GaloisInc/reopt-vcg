def orq : instruction :=
  definst "orq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 8;
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_5 <- eval (bv_or v_3 (sext v_4 64));
      store v_2 v_5 8;
      let (v_7 : expression (bv 1)) <- eval (extract v_3 63 64);
      let (v_8 : expression (bv 1)) <- eval (extract v_4 31 32);
      let (v_9 : expression (bv 1)) <- eval (extract v_3 62 63);
      let (v_10 : expression (bv 1)) <- eval (extract v_4 30 31);
      let (v_11 : expression (bv 1)) <- eval (extract v_3 61 62);
      let (v_12 : expression (bv 1)) <- eval (extract v_4 29 30);
      let (v_13 : expression (bv 1)) <- eval (extract v_3 60 61);
      let (v_14 : expression (bv 1)) <- eval (extract v_4 28 29);
      let (v_15 : expression (bv 1)) <- eval (extract v_3 59 60);
      let (v_16 : expression (bv 1)) <- eval (extract v_4 27 28);
      let (v_17 : expression (bv 1)) <- eval (extract v_3 58 59);
      let (v_18 : expression (bv 1)) <- eval (extract v_4 26 27);
      let (v_19 : expression (bv 1)) <- eval (extract v_3 57 58);
      let (v_20 : expression (bv 1)) <- eval (extract v_4 25 26);
      let (v_21 : expression (bv 1)) <- eval (extract v_3 56 57);
      let (v_22 : expression (bv 1)) <- eval (extract v_4 24 25);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or v_7 v_8) (expression.bv_nat 1 1)) (eq (bv_or v_9 v_10) (expression.bv_nat 1 1)))) (eq (bv_or v_11 v_12) (expression.bv_nat 1 1)))) (eq (bv_or v_13 v_14) (expression.bv_nat 1 1)))) (eq (bv_or v_15 v_16) (expression.bv_nat 1 1)))) (eq (bv_or v_17 v_18) (expression.bv_nat 1 1)))) (eq (bv_or v_19 v_20) (expression.bv_nat 1 1)))) (eq (bv_or v_21 v_22) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      let v_4 <- eval (bv_or v_2 (sext v_3 64));
      let (v_5 : expression (bv 1)) <- eval (extract v_2 63 64);
      let (v_6 : expression (bv 1)) <- eval (extract v_3 31 32);
      let (v_7 : expression (bv 1)) <- eval (extract v_2 62 63);
      let (v_8 : expression (bv 1)) <- eval (extract v_3 30 31);
      let (v_9 : expression (bv 1)) <- eval (extract v_2 61 62);
      let (v_10 : expression (bv 1)) <- eval (extract v_3 29 30);
      let (v_11 : expression (bv 1)) <- eval (extract v_2 60 61);
      let (v_12 : expression (bv 1)) <- eval (extract v_3 28 29);
      let (v_13 : expression (bv 1)) <- eval (extract v_2 59 60);
      let (v_14 : expression (bv 1)) <- eval (extract v_3 27 28);
      let (v_15 : expression (bv 1)) <- eval (extract v_2 58 59);
      let (v_16 : expression (bv 1)) <- eval (extract v_3 26 27);
      let (v_17 : expression (bv 1)) <- eval (extract v_2 57 58);
      let (v_18 : expression (bv 1)) <- eval (extract v_3 25 26);
      let (v_19 : expression (bv 1)) <- eval (extract v_2 56 57);
      let (v_20 : expression (bv 1)) <- eval (extract v_3 24 25);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or v_5 v_6) (expression.bv_nat 1 1)) (eq (bv_or v_7 v_8) (expression.bv_nat 1 1)))) (eq (bv_or v_9 v_10) (expression.bv_nat 1 1)))) (eq (bv_or v_11 v_12) (expression.bv_nat 1 1)))) (eq (bv_or v_13 v_14) (expression.bv_nat 1 1)))) (eq (bv_or v_15 v_16) (expression.bv_nat 1 1)))) (eq (bv_or v_17 v_18) (expression.bv_nat 1 1)))) (eq (bv_or v_19 v_20) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      let v_5 <- eval (bv_or v_2 v_4);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- load v_2 8;
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let v_5 <- eval (bv_or v_3 v_4);
      store v_2 v_5 8;
      let (v_7 : expression (bv 8)) <- eval (extract v_5 56 64);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_1);
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- eval (bv_or v_2 v_3);
      let (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
     action
