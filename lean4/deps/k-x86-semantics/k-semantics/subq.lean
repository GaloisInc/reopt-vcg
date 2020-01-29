def subq : instruction :=
  definst "subq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (sext v_3 64);
      v_5 <- load v_2 8;
      v_6 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_4 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_5));
      (v_7 : expression (bv 64)) <- eval (extract v_6 1 65);
      store v_2 v_7 8;
      v_9 <- eval (isBitSet v_6 1);
      (v_10 : expression (bv 8)) <- eval (extract v_6 57 65);
      (v_11 : expression (bv 1)) <- eval (extract v_4 0 1);
      v_12 <- eval (eq (bv_xor v_11 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_5 59))) (isBitSet v_6 60)));
      setRegister cf (isBitClear v_6 0);
      setRegister of (bit_and (eq v_12 (isBitSet v_5 0)) (notBool_ (eq v_12 v_9)));
      setRegister pf (parityFlag v_10);
      setRegister sf v_9;
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_3 <- eval (sext v_2 64);
      v_4 <- getRegister (lhs.of_reg r64_1);
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 1 65);
      v_7 <- eval (isBitSet v_5 1);
      (v_8 : expression (bv 8)) <- eval (extract v_5 57 65);
      (v_9 : expression (bv 1)) <- eval (extract v_3 0 1);
      v_10 <- eval (eq (bv_xor v_9 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_6;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_2 27) (isBitSet v_4 59))) (isBitSet v_5 60)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_10 (isBitSet v_4 0)) (notBool_ (eq v_10 v_7)));
      setRegister pf (parityFlag v_8);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      v_4 <- getRegister (lhs.of_reg r64_1);
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 1 65);
      v_7 <- eval (isBitSet v_5 1);
      (v_8 : expression (bv 8)) <- eval (extract v_5 57 65);
      (v_9 : expression (bv 1)) <- eval (extract v_3 0 1);
      v_10 <- eval (eq (bv_xor v_9 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 59) (isBitSet v_5 60)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_10 (isBitSet v_4 0)) (notBool_ (eq v_10 v_7)));
      setRegister pf (parityFlag v_8);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r64_0);
      v_4 <- load v_2 8;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 64)) <- eval (extract v_5 1 65);
      store v_2 v_6 8;
      v_8 <- eval (isBitSet v_5 1);
      (v_9 : expression (bv 8)) <- eval (extract v_5 57 65);
      (v_10 : expression (bv 1)) <- eval (extract v_3 0 1);
      v_11 <- eval (eq (bv_xor v_10 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 59) (isBitSet v_5 60)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_11 (isBitSet v_4 0)) (notBool_ (eq v_11 v_8)));
      setRegister pf (parityFlag v_9);
      setRegister sf v_8;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg r64_0);
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3));
      (v_5 : expression (bv 64)) <- eval (extract v_4 1 65);
      v_6 <- eval (isBitSet v_4 1);
      (v_7 : expression (bv 8)) <- eval (extract v_4 57 65);
      (v_8 : expression (bv 1)) <- eval (extract v_2 0 1);
      v_9 <- eval (eq (bv_xor v_8 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 59) (isBitSet v_4 60)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_3 0)) (notBool_ (eq v_9 v_6)));
      setRegister pf (parityFlag v_7);
      setRegister sf v_6;
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
