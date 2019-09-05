def andq1 : instruction :=
  definst "andq" $ do
    pattern fun (v_2908 : imm int) (v_2910 : reg (bv 64)) => do
      v_5436 <- getRegister v_2910;
      v_5437 <- eval (handleImmediateWithSignExtend v_2908 32 32);
      v_5439 <- eval (bv_and v_5436 (sext v_5437 64));
      setRegister (lhs.of_reg v_2910) v_5439;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5436 63 64) (extract v_5437 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5436 62 63) (extract v_5437 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 61 62) (extract v_5437 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 60 61) (extract v_5437 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 59 60) (extract v_5437 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 58 59) (extract v_5437 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 57 58) (extract v_5437 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5436 56 57) (extract v_5437 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_5439 0);
      setRegister zf (zeroFlag v_5439);
      pure ()
    pat_end;
    pattern fun (v_2918 : reg (bv 64)) (v_2919 : reg (bv 64)) => do
      v_5498 <- getRegister v_2919;
      v_5499 <- getRegister v_2918;
      v_5500 <- eval (bv_and v_5498 v_5499);
      setRegister (lhs.of_reg v_2919) v_5500;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5500 56 64));
      setRegister sf (isBitSet v_5500 0);
      setRegister zf (zeroFlag v_5500);
      pure ()
    pat_end;
    pattern fun (v_2913 : Mem) (v_2914 : reg (bv 64)) => do
      v_9208 <- getRegister v_2914;
      v_9209 <- evaluateAddress v_2913;
      v_9210 <- load v_9209 8;
      v_9211 <- eval (bv_and v_9208 v_9210);
      setRegister (lhs.of_reg v_2914) v_9211;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9211 56 64));
      setRegister sf (isBitSet v_9211 0);
      setRegister zf (zeroFlag v_9211);
      pure ()
    pat_end;
    pattern fun (v_2900 : imm int) (v_2901 : Mem) => do
      v_10635 <- evaluateAddress v_2901;
      v_10636 <- load v_10635 8;
      v_10637 <- eval (handleImmediateWithSignExtend v_2900 32 32);
      v_10639 <- eval (bv_and v_10636 (sext v_10637 64));
      store v_10635 v_10639 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_10636 63 64) (extract v_10637 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_10636 62 63) (extract v_10637 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 61 62) (extract v_10637 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 60 61) (extract v_10637 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 59 60) (extract v_10637 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 58 59) (extract v_10637 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 57 58) (extract v_10637 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10636 56 57) (extract v_10637 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_10639 0);
      setRegister zf (zeroFlag v_10639);
      pure ()
    pat_end;
    pattern fun (v_2905 : reg (bv 64)) (v_2904 : Mem) => do
      v_10694 <- evaluateAddress v_2904;
      v_10695 <- load v_10694 8;
      v_10696 <- getRegister v_2905;
      v_10697 <- eval (bv_and v_10695 v_10696);
      store v_10694 v_10697 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10697 56 64));
      setRegister sf (isBitSet v_10697 0);
      setRegister zf (zeroFlag v_10697);
      pure ()
    pat_end
