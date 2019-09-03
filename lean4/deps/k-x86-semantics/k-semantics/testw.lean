def testw1 : instruction :=
  definst "testw" $ do
    pattern fun (v_2468 : imm int) ax => do
      v_4350 <- getRegister rax;
      v_4352 <- eval (handleImmediateWithSignExtend v_2468 16 16);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_4350 63 64) (extract v_4352 15 16)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_4350 62 63) (extract v_4352 14 15)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 61 62) (extract v_4352 13 14)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 60 61) (extract v_4352 12 13)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 59 60) (extract v_4352 11 12)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 58 59) (extract v_4352 10 11)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 57 58) (extract v_4352 9 10)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_4350 56 57) (extract v_4352 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_4350 48 64) v_4352));
      setRegister sf (bv_and (extract v_4350 48 49) (extract v_4352 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2480 : imm int) (v_2484 : reg (bv 16)) => do
      v_4418 <- getRegister v_2484;
      v_4420 <- eval (bv_and v_4418 (handleImmediateWithSignExtend v_2480 16 16));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4420 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_4420);
      setRegister sf (extract v_4420 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2488 : reg (bv 16)) (v_2489 : reg (bv 16)) => do
      v_4431 <- getRegister v_2489;
      v_4432 <- getRegister v_2488;
      v_4433 <- eval (bv_and v_4431 v_4432);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4433 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_4433);
      setRegister sf (extract v_4433 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2473 : imm int) (v_2472 : Mem) => do
      v_8916 <- evaluateAddress v_2472;
      v_8917 <- load v_8916 2;
      v_8919 <- eval (bv_and v_8917 (handleImmediateWithSignExtend v_2473 16 16));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8919 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_8919);
      setRegister sf (extract v_8919 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2479 : reg (bv 16)) (v_2476 : Mem) => do
      v_8930 <- evaluateAddress v_2476;
      v_8931 <- load v_8930 2;
      v_8932 <- getRegister v_2479;
      v_8933 <- eval (bv_and v_8931 v_8932);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8933 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_8933);
      setRegister sf (extract v_8933 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
