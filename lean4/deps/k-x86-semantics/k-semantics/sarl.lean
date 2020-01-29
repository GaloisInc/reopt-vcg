def sarl : instruction :=
  definst "sarl" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- getRegister rcx;
      (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      v_5 <- eval (bv_and v_4 (expression.bv_nat 8 31));
      v_6 <- eval (ashr (concat v_2 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      store v_1 v_7 4;
      v_9 <- eval (eq v_5 (expression.bv_nat 8 0));
      v_10 <- getRegister zf;
      v_11 <- getRegister sf;
      v_12 <- getRegister pf;
      (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      v_14 <- getRegister of;
      v_15 <- getRegister cf;
      v_16 <- getRegister af;
      setRegister af (mux v_9 v_16 undef);
      setRegister cf (mux v_9 v_15 (isBitSet v_6 32));
      setRegister of (bit_and (notBool_ (eq v_5 (expression.bv_nat 8 1))) (mux v_9 v_14 undef));
      setRegister pf (mux v_9 v_12 (parityFlag v_13));
      setRegister sf (mux v_9 v_11 (isBitSet v_6 0));
      setRegister zf (mux v_9 v_10 (eq v_7 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister rcx;
      (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      v_3 <- eval (bv_and v_2 (expression.bv_nat 8 31));
      v_4 <- eval (eq v_3 (expression.bv_nat 8 0));
      v_5 <- getRegister zf;
      v_6 <- getRegister (lhs.of_reg r32_0);
      v_7 <- eval (ashr (concat v_6 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_3));
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      v_9 <- getRegister sf;
      v_10 <- getRegister pf;
      (v_11 : expression (bv 8)) <- eval (extract v_7 24 32);
      v_12 <- getRegister of;
      v_13 <- getRegister cf;
      v_14 <- getRegister af;
      setRegister (lhs.of_reg r32_0) v_8;
      setRegister af (mux v_4 v_14 undef);
      setRegister cf (mux v_4 v_13 (isBitSet v_7 32));
      setRegister of (bit_and (notBool_ (eq v_3 (expression.bv_nat 8 1))) (mux v_4 v_12 undef));
      setRegister pf (mux v_4 v_10 (parityFlag v_11));
      setRegister sf (mux v_4 v_9 (isBitSet v_7 0));
      setRegister zf (mux v_4 v_5 (eq v_8 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 4;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_5 <- eval (ashr (concat v_3 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      store v_2 v_6 4;
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister zf;
      v_10 <- getRegister sf;
      v_11 <- getRegister pf;
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      v_13 <- getRegister of;
      v_14 <- getRegister cf;
      v_15 <- getRegister af;
      setRegister af (mux v_8 v_15 undef);
      setRegister cf (mux v_8 v_14 (isBitSet v_5 32));
      setRegister of (bit_and (notBool_ (eq v_4 (expression.bv_nat 8 1))) (mux v_8 v_13 undef));
      setRegister pf (mux v_8 v_11 (parityFlag v_12));
      setRegister sf (mux v_8 v_10 (isBitSet v_5 0));
      setRegister zf (mux v_8 v_9 (eq v_6 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_4 <- getRegister zf;
      v_5 <- getRegister (lhs.of_reg r32_1);
      v_6 <- eval (ashr (concat v_5 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_2));
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- getRegister sf;
      v_9 <- getRegister pf;
      (v_10 : expression (bv 8)) <- eval (extract v_6 24 32);
      v_11 <- getRegister of;
      v_12 <- getRegister cf;
      v_13 <- getRegister af;
      setRegister (lhs.of_reg r32_1) v_7;
      setRegister af (mux v_3 v_13 undef);
      setRegister cf (mux v_3 v_12 (isBitSet v_6 32));
      setRegister of (bit_and (notBool_ (eq v_2 (expression.bv_nat 8 1))) (mux v_3 v_11 undef));
      setRegister pf (mux v_3 v_9 (parityFlag v_10));
      setRegister sf (mux v_3 v_8 (isBitSet v_6 0));
      setRegister zf (mux v_3 v_4 (eq v_7 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- eval (ashr (concat v_2 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      store v_1 v_4 4;
      (v_6 : expression (bv 8)) <- eval (extract v_3 24 32);
      setRegister af undef;
      setRegister cf (isBitSet v_3 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister (lhs.of_reg r32_0);
      v_2 <- eval (ashr (concat v_1 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_4 : expression (bv 8)) <- eval (extract v_2 24 32);
      setRegister (lhs.of_reg r32_0) v_3;
      setRegister af undef;
      setRegister cf (isBitSet v_2 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_4);
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end
