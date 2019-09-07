def cmpw1 : instruction :=
  definst "cmpw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 2;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (isBitSet v_5 1);
      v_7 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_7 (isBitSet v_4 0)) (notBool_ (eq v_7 v_6)));
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf v_6;
      setRegister zf (zeroFlag (extract v_5 1 17));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 16 16);
      v_3 <- getRegister r16_1;
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (isBitSet v_4 1);
      v_6 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 11) (isBitSet v_4 12)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_6 (isBitSet v_3 0)) (notBool_ (eq v_6 v_5)));
      setRegister pf (parityFlag (extract v_4 9 17));
      setRegister sf v_5;
      setRegister zf (zeroFlag (extract v_4 1 17));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      v_4 <- getRegister r16_1;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (isBitSet v_5 1);
      v_7 <- eval (eq (bv_xor (extract v_3 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_7 (isBitSet v_4 0)) (notBool_ (eq v_7 v_6)));
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf v_6;
      setRegister zf (zeroFlag (extract v_5 1 17));
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- getRegister r16_0;
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 2;
      v_5 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_4));
      v_6 <- eval (isBitSet v_5 1);
      v_7 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_4) 11) (isBitSet v_5 12)));
      setRegister cf (isBitClear v_5 0);
      setRegister of (bit_and (eq v_7 (isBitSet v_4 0)) (notBool_ (eq v_7 v_6)));
      setRegister pf (parityFlag (extract v_5 9 17));
      setRegister sf v_6;
      setRegister zf (zeroFlag (extract v_5 1 17));
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_0;
      v_3 <- getRegister r16_1;
      v_4 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_2 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3));
      v_5 <- eval (isBitSet v_4 1);
      v_6 <- eval (eq (bv_xor (extract v_2 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_2 v_3) 11) (isBitSet v_4 12)));
      setRegister cf (isBitClear v_4 0);
      setRegister of (bit_and (eq v_6 (isBitSet v_3 0)) (notBool_ (eq v_6 v_5)));
      setRegister pf (parityFlag (extract v_4 9 17));
      setRegister sf v_5;
      setRegister zf (zeroFlag (extract v_4 1 17));
      pure ()
    pat_end
