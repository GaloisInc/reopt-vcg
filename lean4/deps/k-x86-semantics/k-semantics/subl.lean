def subl1 : instruction :=
  definst "subl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- load v_2 4;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 33);
      store v_2 v_6 4;
      v_8 <- eval (isBitSet v_5 1);
      v_9 <- eval (eq (bv_xor (extract v_3 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_4 0)) (notBool_ (eq v_9 v_8)));
      setRegister pf (parityFlag (extract v_5 25 33));
      setRegister sf v_8;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_3 <- getRegister r32_1;
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 33);
      v_6 <- eval (isBitSet v_4 1);
      v_7 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 27) (isBitSet v_4 28)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_7 (isBitSet v_3 0)) (notBool_ (eq v_7 v_6)));
      setRegister pf (parityFlag (extract v_4 25 33));
      setRegister sf v_6;
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      v_4 <- getRegister r32_1;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 33);
      v_7 <- eval (isBitSet v_5 1);
      v_8 <- eval (eq (bv_xor (extract v_3 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r32_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_8 (isBitSet v_4 0)) (notBool_ (eq v_8 v_7)));
      setRegister pf (parityFlag (extract v_5 25 33));
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r32_0;
      v_4 <- load v_2 4;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 33);
      store v_2 v_6 4;
      v_8 <- eval (isBitSet v_5 1);
      v_9 <- eval (eq (bv_xor (extract v_3 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_4 0)) (notBool_ (eq v_9 v_8)));
      setRegister pf (parityFlag (extract v_5 25 33));
      setRegister sf v_8;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister r32_0;
      v_3 <- getRegister r32_1;
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 33);
      v_6 <- eval (isBitSet v_4 1);
      v_7 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 27) (isBitSet v_4 28)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_7 (isBitSet v_3 0)) (notBool_ (eq v_7 v_6)));
      setRegister pf (parityFlag (extract v_4 25 33));
      setRegister sf v_6;
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
