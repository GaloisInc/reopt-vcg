def orq1 : instruction :=
  definst "orq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_5 <- eval (bv_or v_3 (sext v_4 64));
      store v_2 v_5 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_3 63 64) (extract v_4 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_3 62 63) (extract v_4 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 61 62) (extract v_4 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 60 61) (extract v_4 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 59 60) (extract v_4 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 58 59) (extract v_4 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 57 58) (extract v_4 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_3 56 57) (extract v_4 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 32 32);
      v_4 <- eval (bv_or v_2 (sext v_3 64));
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_2 63 64) (extract v_3 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_2 62 63) (extract v_3 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 61 62) (extract v_3 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 60 61) (extract v_3 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 59 60) (extract v_3 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 58 59) (extract v_3 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 57 58) (extract v_3 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_2 56 57) (extract v_3 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (bv_or v_2 v_4);
      setRegister (lhs.of_reg r64_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5 56 64));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- getRegister r64_0;
      v_5 <- eval (bv_or v_3 v_4);
      store v_2 v_5 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5 56 64));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- getRegister r64_0;
      v_4 <- eval (bv_or v_2 v_3);
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4 56 64));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end
