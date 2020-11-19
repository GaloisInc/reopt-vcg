def cmpb : instruction :=
  definst "cmpb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 1;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 8)) <- eval (extract v_5 1 9);
      v_7 <- eval (isBitSet v_5 1);
      (v_8 : expression (bv 1)) <- eval (extract v_2 0 1);
      v_9 <- eval (eq (bv_xor v_8 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_4 0)) (notBool_ (eq v_9 v_7)));
      setRegister pf (parityFlag v_6);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister (lhs.of_reg rh_1);
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_3));
      (v_5 : expression (bv 8)) <- eval (extract v_4 1 9);
      v_6 <- eval (isBitSet v_4 1);
      (v_7 : expression (bv 1)) <- eval (extract v_2 0 1);
      v_8 <- eval (eq (bv_xor v_7 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 3) (isBitSet v_4 4)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_8 (isBitSet v_3 0)) (notBool_ (eq v_8 v_6)));
      setRegister pf (parityFlag v_5);
      setRegister sf v_6;
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (rh_1 : reg (bv 8)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 1;
      v_4 <- getRegister (lhs.of_reg rh_1);
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 8)) <- eval (extract v_5 1 9);
      v_7 <- eval (isBitSet v_5 1);
      (v_8 : expression (bv 1)) <- eval (extract v_3 0 1);
      v_9 <- eval (eq (bv_xor v_8 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_4 0)) (notBool_ (eq v_9 v_7)));
      setRegister pf (parityFlag v_6);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (mem_1 : Mem) => do
      v_2 <- getRegister (lhs.of_reg rh_0);
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 1;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_4));
      (v_6 : expression (bv 8)) <- eval (extract v_5 1 9);
      v_7 <- eval (isBitSet v_5 1);
      (v_8 : expression (bv 1)) <- eval (extract v_2 0 1);
      v_9 <- eval (eq (bv_xor v_8 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 3) (isBitSet v_5 4)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_9 (isBitSet v_4 0)) (notBool_ (eq v_9 v_7)));
      setRegister pf (parityFlag v_6);
      setRegister sf v_7;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister (lhs.of_reg rh_0);
      v_3 <- getRegister (lhs.of_reg rh_1);
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_3));
      (v_5 : expression (bv 8)) <- eval (extract v_4 1 9);
      v_6 <- eval (isBitSet v_4 1);
      (v_7 : expression (bv 1)) <- eval (extract v_2 0 1);
      v_8 <- eval (eq (bv_xor v_7 (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 3) (isBitSet v_4 4)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_8 (isBitSet v_3 0)) (notBool_ (eq v_8 v_6)));
      setRegister pf (parityFlag v_5);
      setRegister sf v_6;
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
