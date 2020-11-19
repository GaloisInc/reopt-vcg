def orq : instruction :=
  definst "orq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_5 <- eval (bv_or v_3 (sext v_4 64));
      store v_2 v_5 8;
      (v_7 : expression (bv 1)) <- eval (extract v_3 63 64);
      (v_8 : expression (bv 1)) <- eval (extract v_4 31 32);
      (v_9 : expression (bv 1)) <- eval (extract v_3 62 63);
      (v_10 : expression (bv 1)) <- eval (extract v_4 30 31);
      (v_11 : expression (bv 1)) <- eval (extract v_3 61 62);
      (v_12 : expression (bv 1)) <- eval (extract v_4 29 30);
      (v_13 : expression (bv 1)) <- eval (extract v_3 60 61);
      (v_14 : expression (bv 1)) <- eval (extract v_4 28 29);
      (v_15 : expression (bv 1)) <- eval (extract v_3 59 60);
      (v_16 : expression (bv 1)) <- eval (extract v_4 27 28);
      (v_17 : expression (bv 1)) <- eval (extract v_3 58 59);
      (v_18 : expression (bv 1)) <- eval (extract v_4 26 27);
      (v_19 : expression (bv 1)) <- eval (extract v_3 57 58);
      (v_20 : expression (bv 1)) <- eval (extract v_4 25 26);
      (v_21 : expression (bv 1)) <- eval (extract v_3 56 57);
      (v_22 : expression (bv 1)) <- eval (extract v_4 24 25);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or v_7 v_8) (expression.bv_nat 1 1)) (eq (bv_or v_9 v_10) (expression.bv_nat 1 1)))) (eq (bv_or v_11 v_12) (expression.bv_nat 1 1)))) (eq (bv_or v_13 v_14) (expression.bv_nat 1 1)))) (eq (bv_or v_15 v_16) (expression.bv_nat 1 1)))) (eq (bv_or v_17 v_18) (expression.bv_nat 1 1)))) (eq (bv_or v_19 v_20) (expression.bv_nat 1 1)))) (eq (bv_or v_21 v_22) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg r64_1);
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (bv_or v_2 (sext v_3 64));
      (v_5 : expression (bv 1)) <- eval (extract v_2 63 64);
      (v_6 : expression (bv 1)) <- eval (extract v_3 31 32);
      (v_7 : expression (bv 1)) <- eval (extract v_2 62 63);
      (v_8 : expression (bv 1)) <- eval (extract v_3 30 31);
      (v_9 : expression (bv 1)) <- eval (extract v_2 61 62);
      (v_10 : expression (bv 1)) <- eval (extract v_3 29 30);
      (v_11 : expression (bv 1)) <- eval (extract v_2 60 61);
      (v_12 : expression (bv 1)) <- eval (extract v_3 28 29);
      (v_13 : expression (bv 1)) <- eval (extract v_2 59 60);
      (v_14 : expression (bv 1)) <- eval (extract v_3 27 28);
      (v_15 : expression (bv 1)) <- eval (extract v_2 58 59);
      (v_16 : expression (bv 1)) <- eval (extract v_3 26 27);
      (v_17 : expression (bv 1)) <- eval (extract v_2 57 58);
      (v_18 : expression (bv 1)) <- eval (extract v_3 25 26);
      (v_19 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_20 : expression (bv 1)) <- eval (extract v_3 24 25);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or v_5 v_6) (expression.bv_nat 1 1)) (eq (bv_or v_7 v_8) (expression.bv_nat 1 1)))) (eq (bv_or v_9 v_10) (expression.bv_nat 1 1)))) (eq (bv_or v_11 v_12) (expression.bv_nat 1 1)))) (eq (bv_or v_13 v_14) (expression.bv_nat 1 1)))) (eq (bv_or v_15 v_16) (expression.bv_nat 1 1)))) (eq (bv_or v_17 v_18) (expression.bv_nat 1 1)))) (eq (bv_or v_19 v_20) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg r64_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (bv_or v_2 v_4);
      (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- eval (bv_or v_3 v_4);
      store v_2 v_5 8;
      (v_7 : expression (bv 8)) <- eval (extract v_5 56 64);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg r64_1);
      v_3 <- getRegister (lhs.of_reg r64_0);
      v_4 <- eval (bv_or v_2 v_3);
      (v_5 : expression (bv 8)) <- eval (extract v_4 56 64);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end
