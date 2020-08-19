def sbbq : instruction :=
  definst "sbbq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_5 <- eval (sext v_4 64);
      v_6 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_5 (expression.bv_nat 64 18446744073709551615)));
      v_7 <- load v_2 8;
      v_8 <- eval (add (mux v_3 v_6 (add v_6 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_7));
      (v_9 : expression (bv 64)) <- eval (extract v_8 1 65);
      store v_2 v_9 8;
      v_11 <- eval (isBitSet v_8 1);
      (v_12 : expression (bv 8)) <- eval (extract v_8 57 65);
      (v_13 : expression (bv 1)) <- eval (extract v_5 0 1);
      v_14 <- eval (eq (bv_xor v_13 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4 27) (isBitSet v_7 59))) (isBitSet v_8 60)));
      setRegister cf (isBitClear v_8 0);
      setRegister of (bit_and (eq v_14 (isBitSet v_7 0)) (notBool_ (eq v_14 v_11)));
      setRegister pf (parityFlag v_12);
      setRegister sf v_11;
      setRegister zf (zeroFlag v_9);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (sext v_3 64);
      v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      v_6 <- getRegister (lhs.of_reg r64_1);
      v_7 <- eval (add (mux v_2 v_5 (add v_5 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      v_9 <- eval (isBitSet v_7 1);
      (v_10 : expression (bv 8)) <- eval (extract v_7 57 65);
      (v_11 : expression (bv 1)) <- eval (extract v_4 0 1);
      v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_6 59))) (isBitSet v_7 60)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_6 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      v_6 <- getRegister (lhs.of_reg r64_1);
      v_7 <- eval (add (mux v_2 v_5 (add v_5 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      v_9 <- eval (isBitSet v_7 1);
      (v_10 : expression (bv 8)) <- eval (extract v_7 57 65);
      (v_11 : expression (bv 1)) <- eval (extract v_4 0 1);
      v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_7 60)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_6 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615)));
      v_6 <- load v_2 8;
      v_7 <- eval (add (mux v_3 v_5 (add v_5 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 64)) <- eval (extract v_7 1 65);
      store v_2 v_8 8;
      v_10 <- eval (isBitSet v_7 1);
      (v_11 : expression (bv 8)) <- eval (extract v_7 57 65);
      (v_12 : expression (bv 1)) <- eval (extract v_4 0 1);
      v_13 <- eval (eq (bv_xor v_12 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_7 60)));
      setRegister cf (isBitClear v_7 0);
      setRegister of (bit_and (eq v_13 (isBitSet v_6 0)) (notBool_ (eq v_13 v_10)));
      setRegister pf (parityFlag v_11);
      setRegister sf v_10;
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister (lhs.of_reg r64_0);
      v_4 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615)));
      v_5 <- getRegister (lhs.of_reg r64_1);
      v_6 <- eval (add (mux v_2 v_4 (add v_4 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_5));
      (v_7 : expression (bv 64)) <- eval (extract v_6 1 65);
      v_8 <- eval (isBitSet v_6 1);
      (v_9 : expression (bv 8)) <- eval (extract v_6 57 65);
      (v_10 : expression (bv 1)) <- eval (extract v_3 0 1);
      v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 59) (isBitSet v_6 60)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_5 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end