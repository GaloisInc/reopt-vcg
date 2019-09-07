def adcl1 : instruction :=
  definst "adcl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- load v_2 4;
      v_7 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 33 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 33);
      store v_2 v_8 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_7 28)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 25 33));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister cf;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      v_5 <- getRegister r32_1;
      v_6 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 33 1)) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 33);
      setRegister (lhs.of_reg r32_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 27) (isBitSet v_6 28)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_3 v_5 v_7);
      setRegister pf (parityFlag (extract v_6 25 33));
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister cf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- getRegister r32_1;
      v_7 <- eval (add (mux v_2 (add v_5 (expression.bv_nat 33 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 33);
      setRegister (lhs.of_reg r32_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_7 28)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 25 33));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- getRegister r32_0;
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- load v_2 4;
      v_7 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 33 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 33);
      store v_2 v_8 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 27) (isBitSet v_7 28)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag (extract v_7 25 33));
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister r32_0;
      v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      v_5 <- getRegister r32_1;
      v_6 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 33 1)) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 33);
      setRegister (lhs.of_reg r32_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 27) (isBitSet v_6 28)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_3 v_5 v_7);
      setRegister pf (parityFlag (extract v_6 25 33));
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end
