def adcb : instruction :=
  definst "adcb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- load v_2 1;
      v_7 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 9 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 9);
      store v_2 v_8 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister cf;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      v_5 <- getRegister (lhs.of_reg rh_1);
      v_6 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 9 1)) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 9);
      setRegister (lhs.of_reg rh_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 3) (isBitSet v_6 4)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_3 v_5 v_7);
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister cf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 1;
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- getRegister (lhs.of_reg rh_1);
      v_7 <- eval (add (mux v_2 (add v_5 (expression.bv_nat 9 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 9);
      setRegister (lhs.of_reg rh_1) v_8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- getRegister (lhs.of_reg rh_0);
      v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      v_6 <- load v_2 1;
      v_7 <- eval (add (mux v_3 (add v_5 (expression.bv_nat 9 1)) v_5) (concat (expression.bv_nat 1 0) v_6));
      v_8 <- eval (extract v_7 1 9);
      store v_2 v_8 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4 v_6) 3) (isBitSet v_7 4)));
      setRegister cf (isBitSet v_7 0);
      setRegister of (overflowFlag v_4 v_6 v_8);
      setRegister pf (parityFlag v_8);
      setRegister sf (isBitSet v_7 1);
      setRegister zf (zeroFlag v_8);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister (lhs.of_reg rh_0);
      v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      v_5 <- getRegister (lhs.of_reg rh_1);
      v_6 <- eval (add (mux v_2 (add v_4 (expression.bv_nat 9 1)) v_4) (concat (expression.bv_nat 1 0) v_5));
      v_7 <- eval (extract v_6 1 9);
      setRegister (lhs.of_reg rh_1) v_7;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_5) 3) (isBitSet v_6 4)));
      setRegister cf (isBitSet v_6 0);
      setRegister of (overflowFlag v_3 v_5 v_7);
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_6 1);
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end
