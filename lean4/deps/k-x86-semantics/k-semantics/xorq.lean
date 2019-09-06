def xorq1 : instruction :=
  definst "xorq" $ do
    pattern fun (v_3465 : imm int) (v_3466 : reg (bv 64)) => do
      v_8074 <- getRegister v_3466;
      v_8075 <- eval (handleImmediateWithSignExtend v_3465 32 32);
      v_8077 <- eval (bv_xor v_8074 (sext v_8075 64));
      setRegister (lhs.of_reg v_3466) v_8077;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_8074 63 64) (extract v_8075 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_8074 62 63) (extract v_8075 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 61 62) (extract v_8075 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 60 61) (extract v_8075 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 59 60) (extract v_8075 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 58 59) (extract v_8075 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 57 58) (extract v_8075 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8074 56 57) (extract v_8075 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_8077 0);
      setRegister zf (zeroFlag v_8077);
      pure ()
    pat_end;
    pattern fun (v_3474 : reg (bv 64)) (v_3475 : reg (bv 64)) => do
      v_8136 <- getRegister v_3475;
      v_8137 <- getRegister v_3474;
      v_8138 <- eval (bv_xor v_8136 v_8137);
      setRegister (lhs.of_reg v_3475) v_8138;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8138 56 64));
      setRegister sf (isBitSet v_8138 0);
      setRegister zf (zeroFlag v_8138);
      pure ()
    pat_end;
    pattern fun (v_3470 : Mem) (v_3471 : reg (bv 64)) => do
      v_13601 <- getRegister v_3471;
      v_13602 <- evaluateAddress v_3470;
      v_13603 <- load v_13602 8;
      v_13604 <- eval (bv_xor v_13601 v_13603);
      setRegister (lhs.of_reg v_3471) v_13604;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13604 56 64));
      setRegister sf (isBitSet v_13604 0);
      setRegister zf (zeroFlag v_13604);
      pure ()
    pat_end;
    pattern fun (v_3457 : imm int) (v_3458 : Mem) => do
      v_13708 <- evaluateAddress v_3458;
      v_13709 <- load v_13708 8;
      v_13710 <- eval (handleImmediateWithSignExtend v_3457 32 32);
      v_13712 <- eval (bv_xor v_13709 (sext v_13710 64));
      store v_13708 v_13712 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_13709 63 64) (extract v_13710 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_13709 62 63) (extract v_13710 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 61 62) (extract v_13710 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 60 61) (extract v_13710 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 59 60) (extract v_13710 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 58 59) (extract v_13710 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 57 58) (extract v_13710 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13709 56 57) (extract v_13710 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_13712 0);
      setRegister zf (zeroFlag v_13712);
      pure ()
    pat_end;
    pattern fun (v_3462 : reg (bv 64)) (v_3461 : Mem) => do
      v_13767 <- evaluateAddress v_3461;
      v_13768 <- load v_13767 8;
      v_13769 <- getRegister v_3462;
      v_13770 <- eval (bv_xor v_13768 v_13769);
      store v_13767 v_13770 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13770 56 64));
      setRegister sf (isBitSet v_13770 0);
      setRegister zf (zeroFlag v_13770);
      pure ()
    pat_end
