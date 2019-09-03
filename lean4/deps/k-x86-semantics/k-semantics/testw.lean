def testw1 : instruction :=
  definst "testw" $ do
    pattern fun (v_2482 : imm int) ax => do
      v_4361 <- getRegister rax;
      v_4363 <- eval (handleImmediateWithSignExtend v_2482 16 16);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4361 63 64) (extract v_4363 15 16)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4361 62 63) (extract v_4363 14 15)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 61 62) (extract v_4363 13 14)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 60 61) (extract v_4363 12 13)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 59 60) (extract v_4363 11 12)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 58 59) (extract v_4363 10 11)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 57 58) (extract v_4363 9 10)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4361 56 57) (extract v_4363 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_4361 48 64) v_4363));
      setRegister sf (bv_and (extract v_4361 48 49) (extract v_4363 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2494 : imm int) (v_2497 : reg (bv 16)) => do
      v_4429 <- getRegister v_2497;
      v_4431 <- eval (bv_and v_4429 (handleImmediateWithSignExtend v_2494 16 16));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4431 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_4431);
      setRegister sf (extract v_4431 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2501 : reg (bv 16)) (v_2502 : reg (bv 16)) => do
      v_4442 <- getRegister v_2502;
      v_4443 <- getRegister v_2501;
      v_4444 <- eval (bv_and v_4442 v_4443);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4444 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_4444);
      setRegister sf (extract v_4444 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2486 : imm int) (v_2485 : Mem) => do
      v_10010 <- evaluateAddress v_2485;
      v_10011 <- load v_10010 2;
      v_10013 <- eval (bv_and v_10011 (handleImmediateWithSignExtend v_2486 16 16));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10013 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_10013);
      setRegister sf (extract v_10013 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2492 : reg (bv 16)) (v_2489 : Mem) => do
      v_10024 <- evaluateAddress v_2489;
      v_10025 <- load v_10024 2;
      v_10026 <- getRegister v_2492;
      v_10027 <- eval (bv_and v_10025 v_10026);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10027 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_10027);
      setRegister sf (extract v_10027 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
