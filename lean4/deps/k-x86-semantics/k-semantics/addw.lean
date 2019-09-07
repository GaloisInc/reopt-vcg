def addw1 : instruction :=
  definst "addw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      v_4 <- load v_2 2;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 17);
      store v_2 v_6 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      v_3 <- getRegister r16_1;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 17);
      setRegister (lhs.of_reg r16_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 11) (isBitSet v_4 12)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag (extract v_4 9 17));
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      v_4 <- getRegister r16_1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 17);
      setRegister (lhs.of_reg r16_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r16_0;
      v_4 <- load v_2 2;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 17);
      store v_2 v_6 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_0;
      v_3 <- getRegister r16_1;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 17);
      setRegister (lhs.of_reg r16_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 11) (isBitSet v_4 12)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag (extract v_4 9 17));
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
