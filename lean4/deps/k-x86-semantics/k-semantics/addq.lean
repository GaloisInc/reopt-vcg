def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (sext v_3 64);
      v_5 <- load v_2 8;
      v_6 <- eval (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 65);
      store v_2 v_7 8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_5 59))) (isBitSet v_6 60)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_4 v_5 v_7);
      setRegister pf (parityFlag (extract v_6 57 65));
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_3 <- eval (sext v_2 64);
      v_4 <- getRegister r64_1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 65);
      setRegister (lhs.of_reg r64_1) v_6;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_2 27) (isBitSet v_4 59))) (isBitSet v_5 60)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 57 65));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      v_4 <- getRegister r64_1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 65);
      setRegister (lhs.of_reg r64_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 59) (isBitSet v_5 60)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 57 65));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      v_4 <- load v_2 8;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 65);
      store v_2 v_6 8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 59) (isBitSet v_5 60)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 57 65));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_0;
      v_3 <- getRegister r64_1;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 65);
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 59) (isBitSet v_4 60)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag (extract v_4 57 65));
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
