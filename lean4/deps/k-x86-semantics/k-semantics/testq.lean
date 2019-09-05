def testq1 : instruction :=
  definst "testq" $ do
    pattern fun (v_2520 : imm int) (v_2522 : reg (bv 64)) => do
      v_4284 <- getRegister v_2522;
      v_4285 <- eval (handleImmediateWithSignExtend v_2520 32 32);
      v_4287 <- eval (bv_and v_4284 (sext v_4285 64));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4284 63 64) (extract v_4285 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4284 62 63) (extract v_4285 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 61 62) (extract v_4285 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 60 61) (extract v_4285 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 59 60) (extract v_4285 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 58 59) (extract v_4285 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 57 58) (extract v_4285 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4284 56 57) (extract v_4285 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4287 0);
      setRegister zf (zeroFlag v_4287);
      pure ()
    pat_end;
    pattern fun (v_2526 : reg (bv 64)) (v_2527 : reg (bv 64)) => do
      v_4341 <- getRegister v_2527;
      v_4342 <- getRegister v_2526;
      v_4343 <- eval (bv_and v_4341 v_4342);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4343 56 64));
      setRegister sf (isBitSet v_4343 0);
      setRegister zf (zeroFlag v_4343);
      pure ()
    pat_end;
    pattern fun (v_2513 : imm int) (v_2512 : Mem) => do
      v_8744 <- evaluateAddress v_2512;
      v_8745 <- load v_8744 8;
      v_8746 <- eval (handleImmediateWithSignExtend v_2513 32 32);
      v_8748 <- eval (bv_and v_8745 (sext v_8746 64));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_8745 63 64) (extract v_8746 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_8745 62 63) (extract v_8746 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 61 62) (extract v_8746 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 60 61) (extract v_8746 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 59 60) (extract v_8746 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 58 59) (extract v_8746 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 57 58) (extract v_8746 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8745 56 57) (extract v_8746 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_8748 0);
      setRegister zf (zeroFlag v_8748);
      pure ()
    pat_end;
    pattern fun (v_2517 : reg (bv 64)) (v_2516 : Mem) => do
      v_8802 <- evaluateAddress v_2516;
      v_8803 <- load v_8802 8;
      v_8804 <- getRegister v_2517;
      v_8805 <- eval (bv_and v_8803 v_8804);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8805 56 64));
      setRegister sf (isBitSet v_8805 0);
      setRegister zf (zeroFlag v_8805);
      pure ()
    pat_end
