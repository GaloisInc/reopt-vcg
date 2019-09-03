def testq1 : instruction :=
  definst "testq" $ do
    pattern fun (v_2454 : imm int) (v_2456 : reg (bv 64)) => do
      v_4219 <- getRegister v_2456;
      v_4220 <- eval (handleImmediateWithSignExtend v_2454 32 32);
      v_4223 <- eval (bv_and v_4219 (mi 64 (svalueMInt v_4220)));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4219 63 64) (extract v_4220 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4219 62 63) (extract v_4220 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 61 62) (extract v_4220 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 60 61) (extract v_4220 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 59 60) (extract v_4220 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 58 59) (extract v_4220 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 57 58) (extract v_4220 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4219 56 57) (extract v_4220 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_4223);
      setRegister sf (extract v_4223 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2460 : reg (bv 64)) (v_2461 : reg (bv 64)) => do
      v_4278 <- getRegister v_2461;
      v_4279 <- getRegister v_2460;
      v_4280 <- eval (bv_and v_4278 v_4279);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4280 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_4280);
      setRegister sf (extract v_4280 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2447 : imm int) (v_2446 : Mem) => do
      v_8842 <- evaluateAddress v_2446;
      v_8843 <- load v_8842 8;
      v_8844 <- eval (handleImmediateWithSignExtend v_2447 32 32);
      v_8847 <- eval (bv_and v_8843 (mi 64 (svalueMInt v_8844)));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_8843 63 64) (extract v_8844 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_8843 62 63) (extract v_8844 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 61 62) (extract v_8844 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 60 61) (extract v_8844 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 59 60) (extract v_8844 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 58 59) (extract v_8844 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 57 58) (extract v_8844 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_8843 56 57) (extract v_8844 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_8847);
      setRegister sf (extract v_8847 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2451 : reg (bv 64)) (v_2450 : Mem) => do
      v_8902 <- evaluateAddress v_2450;
      v_8903 <- load v_8902 8;
      v_8904 <- getRegister v_2451;
      v_8905 <- eval (bv_and v_8903 v_8904);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8905 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_8905);
      setRegister sf (extract v_8905 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
