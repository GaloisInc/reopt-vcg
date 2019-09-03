def testq1 : instruction :=
  definst "testq" $ do
    pattern fun (v_2469 : imm int) (v_2467 : reg (bv 64)) => do
      v_4232 <- getRegister v_2467;
      v_4233 <- eval (handleImmediateWithSignExtend v_2469 32 32);
      v_4235 <- eval (bv_and v_4232 (leanSignExtend v_4233 64));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4232 63 64) (extract v_4233 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4232 62 63) (extract v_4233 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 61 62) (extract v_4233 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 60 61) (extract v_4233 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 59 60) (extract v_4233 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 58 59) (extract v_4233 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 57 58) (extract v_4233 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4232 56 57) (extract v_4233 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_4235);
      setRegister sf (extract v_4235 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2472 : reg (bv 64)) (v_2473 : reg (bv 64)) => do
      v_4290 <- getRegister v_2473;
      v_4291 <- getRegister v_2472;
      v_4292 <- eval (bv_and v_4290 v_4291);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4292 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_4292);
      setRegister sf (extract v_4292 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2460 : imm int) (v_2459 : Mem) => do
      v_9937 <- evaluateAddress v_2459;
      v_9938 <- load v_9937 8;
      v_9939 <- eval (handleImmediateWithSignExtend v_2460 32 32);
      v_9941 <- eval (bv_and v_9938 (leanSignExtend v_9939 64));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_9938 63 64) (extract v_9939 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_9938 62 63) (extract v_9939 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 61 62) (extract v_9939 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 60 61) (extract v_9939 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 59 60) (extract v_9939 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 58 59) (extract v_9939 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 57 58) (extract v_9939 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_9938 56 57) (extract v_9939 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_9941);
      setRegister sf (extract v_9941 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2464 : reg (bv 64)) (v_2463 : Mem) => do
      v_9996 <- evaluateAddress v_2463;
      v_9997 <- load v_9996 8;
      v_9998 <- getRegister v_2464;
      v_9999 <- eval (bv_and v_9997 v_9998);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9999 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_9999);
      setRegister sf (extract v_9999 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
