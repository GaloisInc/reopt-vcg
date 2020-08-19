def addl : instruction :=
  definst "addl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- load v_2 4;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_5 1 33);
      store v_2 v_6 4;
      (v_8 : expression (bv 8)) <- eval (extract v_5 25 33);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      (v_5 : expression (bv 32)) <- eval (extract v_4 1 33);
      (v_6 : expression (bv 8)) <- eval (extract v_4 25 33);
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 27) (isBitSet v_4 28)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      v_4 <- getRegister (lhs.of_reg r32_1);
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_5 1 33);
      (v_7 : expression (bv 8)) <- eval (extract v_5 25 33);
      setRegister (lhs.of_reg r32_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r32_0);
      v_4 <- load v_2 4;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_5 1 33);
      store v_2 v_6 4;
      (v_8 : expression (bv 8)) <- eval (extract v_5 25 33);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 27) (isBitSet v_5 28)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg r32_0);
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      (v_5 : expression (bv 32)) <- eval (extract v_4 1 33);
      (v_6 : expression (bv 8)) <- eval (extract v_4 25 33);
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 27) (isBitSet v_4 28)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end