def adcq1 : instruction :=
  definst "adcq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_5 <- eval (sext v_4 64);
      v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      v_7 <- load v_2 8;
      v_8 <- eval (add (mux v_3 (add v_6 (expression.bv_nat 65 1)) v_6) (concat (expression.bv_nat 1 0) v_7));
      v_9 <- eval (extract v_8 1 65);
      store v_2 v_9 8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4 27) (isBitSet v_7 59))) (isBitSet v_8 60)));
      setRegister cf (isBitSet v_8 0);
      setRegister of (overflowFlag v_5 v_7 v_9);
      setRegister pf (parityFlag (extract v_8 57 65));
      setRegister sf (isBitSet v_8 1);
      setRegister zf (zeroFlag v_9);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (sext v_3 64);
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- getRegister r64_1;
      v_7 <- eval (add (mux v_2 (add v_5 (expression.bv_nat 65 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 65);
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3 27) (isBitSet v_6 59))) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 57 65));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- getRegister r64_1;
      v_7 <- eval (add (mux v_2 (add v_5 (expression.bv_nat 65 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 65);
      setRegister (lhs.of_reg r64_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 57 65));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- getRegister r64_0;
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- load v_2 8;
      v_7 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 65 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 65);
      store v_2 v_8 8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 59) (isBitSet v_7 60)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 57 65));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister r64_0;
      v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      v_5 <- getRegister r64_1;
      v_6 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 65 1)) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 65);
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 59) (isBitSet v_6 60)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_3 v_5 v_7);
      setRegister pf (parityFlag (extract v_6 57 65));
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end
