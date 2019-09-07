def addb1 : instruction :=
  definst "addb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- load v_2 1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 9);
      store v_2 v_6 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister rh_1;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 9);
      setRegister (lhs.of_reg rh_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 3) (isBitSet v_4 4)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (rh_1 : reg (bv 8)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 1;
      v_4 <- getRegister rh_1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 9);
      setRegister (lhs.of_reg rh_1) v_6;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister rh_0;
      v_4 <- load v_2 1;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (extract v_5 1 9);
      store v_2 v_6 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitSet v_5 0);
      setRegister of (overflowFlag v_3 v_4 v_6);
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 1);
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister rh_0;
      v_3 <- getRegister rh_1;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (extract v_4 1 9);
      setRegister (lhs.of_reg rh_1) v_5;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 3) (isBitSet v_4 4)));
      setRegister cf (isBitSet v_4 0);
      setRegister of (overflowFlag v_2 v_3 v_5);
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 1);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
