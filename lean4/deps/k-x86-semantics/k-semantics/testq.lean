def testq1 : instruction :=
  definst "testq" $ do
    pattern fun (v_2546 : imm int) (v_2545 : reg (bv 64)) => do
      v_4311 <- getRegister v_2545;
      v_4312 <- eval (handleImmediateWithSignExtend v_2546 32 32);
      v_4314 <- eval (bv_and v_4311 (sext v_4312 64));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4311 63 64) (extract v_4312 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4311 62 63) (extract v_4312 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 61 62) (extract v_4312 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 60 61) (extract v_4312 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 59 60) (extract v_4312 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 58 59) (extract v_4312 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 57 58) (extract v_4312 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4311 56 57) (extract v_4312 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4314 0);
      setRegister zf (zeroFlag v_4314);
      pure ()
    pat_end;
    pattern fun (v_2550 : reg (bv 64)) (v_2551 : reg (bv 64)) => do
      v_4368 <- getRegister v_2551;
      v_4369 <- getRegister v_2550;
      v_4370 <- eval (bv_and v_4368 v_4369);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4370 56 64));
      setRegister sf (isBitSet v_4370 0);
      setRegister zf (zeroFlag v_4370);
      pure ()
    pat_end;
    pattern fun (v_2538 : imm int) (v_2537 : Mem) => do
      v_8771 <- evaluateAddress v_2537;
      v_8772 <- load v_8771 8;
      v_8773 <- eval (handleImmediateWithSignExtend v_2538 32 32);
      v_8775 <- eval (bv_and v_8772 (sext v_8773 64));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_8772 63 64) (extract v_8773 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_8772 62 63) (extract v_8773 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 61 62) (extract v_8773 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 60 61) (extract v_8773 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 59 60) (extract v_8773 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 58 59) (extract v_8773 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 57 58) (extract v_8773 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8772 56 57) (extract v_8773 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_8775 0);
      setRegister zf (zeroFlag v_8775);
      pure ()
    pat_end;
    pattern fun (v_2542 : reg (bv 64)) (v_2541 : Mem) => do
      v_8829 <- evaluateAddress v_2541;
      v_8830 <- load v_8829 8;
      v_8831 <- getRegister v_2542;
      v_8832 <- eval (bv_and v_8830 v_8831);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8832 56 64));
      setRegister sf (isBitSet v_8832 0);
      setRegister zf (zeroFlag v_8832);
      pure ()
    pat_end
