def sarq : instruction :=
  definst "sarq" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 8;
      v_3 <- getRegister rcx;
      v_4 <- eval (bv_and (extract v_3 56 64) (expression.bv_nat 8 63));
      v_5 <- eval (ashr (concat v_2 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_4));
      v_6 <- eval (extract v_5 0 64);
      store v_1 v_6 8;
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister zf;
      v_10 <- getRegister sf;
      v_11 <- getRegister pf;
      v_12 <- getRegister of;
      v_13 <- getRegister cf;
      v_14 <- getRegister af;
      setRegister af (mux v_8 v_14 undef);
      setRegister cf (mux v_8 v_13 (isBitSet v_5 64));
      setRegister of (bit_and (notBool_ (eq v_4 (expression.bv_nat 8 1))) (mux v_8 v_12 undef));
      setRegister pf (mux v_8 v_11 (parityFlag (extract v_5 56 64)));
      setRegister sf (mux v_8 v_10 (isBitSet v_5 0));
      setRegister zf (mux v_8 v_9 (eq v_6 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister rcx;
      v_2 <- eval (bv_and (extract v_1 56 64) (expression.bv_nat 8 63));
      v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_4 <- getRegister zf;
      v_5 <- getRegister (lhs.of_reg r64_0);
      v_6 <- eval (ashr (concat v_5 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_2));
      v_7 <- eval (extract v_6 0 64);
      v_8 <- getRegister sf;
      v_9 <- getRegister pf;
      v_10 <- getRegister of;
      v_11 <- getRegister cf;
      v_12 <- getRegister af;
      setRegister (lhs.of_reg r64_0) v_7;
      setRegister af (mux v_3 v_12 undef);
      setRegister cf (mux v_3 v_11 (isBitSet v_6 64));
      setRegister of (bit_and (notBool_ (eq v_2 (expression.bv_nat 8 1))) (mux v_3 v_10 undef));
      setRegister pf (mux v_3 v_9 (parityFlag (extract v_6 56 64)));
      setRegister sf (mux v_3 v_8 (isBitSet v_6 0));
      setRegister zf (mux v_3 v_4 (eq v_7 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      v_5 <- eval (ashr (concat v_3 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_4));
      v_6 <- eval (extract v_5 0 64);
      store v_2 v_6 8;
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister zf;
      v_10 <- getRegister sf;
      v_11 <- getRegister pf;
      v_12 <- getRegister of;
      v_13 <- getRegister cf;
      v_14 <- getRegister af;
      setRegister af (mux v_8 v_14 undef);
      setRegister cf (mux v_8 v_13 (isBitSet v_5 64));
      setRegister of (bit_and (notBool_ (eq v_4 (expression.bv_nat 8 1))) (mux v_8 v_12 undef));
      setRegister pf (mux v_8 v_11 (parityFlag (extract v_5 56 64)));
      setRegister sf (mux v_8 v_10 (isBitSet v_5 0));
      setRegister zf (mux v_8 v_9 (eq v_6 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_4 <- getRegister zf;
      v_5 <- getRegister (lhs.of_reg r64_1);
      v_6 <- eval (ashr (concat v_5 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_2));
      v_7 <- eval (extract v_6 0 64);
      v_8 <- getRegister sf;
      v_9 <- getRegister pf;
      v_10 <- getRegister of;
      v_11 <- getRegister cf;
      v_12 <- getRegister af;
      setRegister (lhs.of_reg r64_1) v_7;
      setRegister af (mux v_3 v_12 undef);
      setRegister cf (mux v_3 v_11 (isBitSet v_6 64));
      setRegister of (bit_and (notBool_ (eq v_2 (expression.bv_nat 8 1))) (mux v_3 v_10 undef));
      setRegister pf (mux v_3 v_9 (parityFlag (extract v_6 56 64)));
      setRegister sf (mux v_3 v_8 (isBitSet v_6 0));
      setRegister zf (mux v_3 v_4 (eq v_7 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 8;
      v_3 <- eval (ashr (concat v_2 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_4 <- eval (extract v_3 0 64);
      store v_1 v_4 8;
      setRegister af undef;
      setRegister cf (isBitSet v_3 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_3 56 64));
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister (lhs.of_reg r64_0);
      v_2 <- eval (ashr (concat v_1 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_3 <- eval (extract v_2 0 64);
      setRegister (lhs.of_reg r64_0) v_3;
      setRegister af undef;
      setRegister cf (isBitSet v_2 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_2 56 64));
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end
