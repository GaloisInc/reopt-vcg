def testl1 : instruction :=
  definst "testl" $ do
    pattern fun (v_2438 : imm int) eax => do
      v_4130 <- getRegister rax;
      v_4132 <- eval (handleImmediateWithSignExtend v_2438 32 32);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4130 63 64) (extract v_4132 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4130 62 63) (extract v_4132 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 61 62) (extract v_4132 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 60 61) (extract v_4132 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 59 60) (extract v_4132 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 58 59) (extract v_4132 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 57 58) (extract v_4132 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4130 56 57) (extract v_4132 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_4130 32 64) v_4132));
      setRegister sf (bv_and (extract v_4130 32 33) (extract v_4132 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2451 : imm int) (v_2449 : reg (bv 32)) => do
      v_4198 <- getRegister v_2449;
      v_4200 <- eval (bv_and v_4198 (handleImmediateWithSignExtend v_2451 32 32));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4200 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4200);
      setRegister sf (extract v_4200 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2454 : reg (bv 32)) (v_2455 : reg (bv 32)) => do
      v_4211 <- getRegister v_2455;
      v_4212 <- getRegister v_2454;
      v_4213 <- eval (bv_and v_4211 v_4212);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4213 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4213);
      setRegister sf (extract v_4213 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2442 : imm int) (v_2441 : Mem) => do
      v_9909 <- evaluateAddress v_2441;
      v_9910 <- load v_9909 4;
      v_9912 <- eval (bv_and v_9910 (handleImmediateWithSignExtend v_2442 32 32));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9912 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9912);
      setRegister sf (extract v_9912 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2445 : reg (bv 32)) (v_2446 : Mem) => do
      v_9923 <- evaluateAddress v_2446;
      v_9924 <- load v_9923 4;
      v_9925 <- getRegister v_2445;
      v_9926 <- eval (bv_and v_9924 v_9925);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9926 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9926);
      setRegister sf (extract v_9926 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
