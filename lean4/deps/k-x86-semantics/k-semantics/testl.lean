def testl1 : instruction :=
  definst "testl" $ do
    pattern fun (v_2527 : imm int) (v_2531 : reg (bv 32)) => do
      v_4277 <- getRegister v_2531;
      v_4279 <- eval (bv_and v_4277 (handleImmediateWithSignExtend v_2527 32 32));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4279 24 32));
      setRegister sf (isBitSet v_4279 0);
      setRegister zf (zeroFlag v_4279);
      pure ()
    pat_end;
    pattern fun (v_2535 : reg (bv 32)) (v_2536 : reg (bv 32)) => do
      v_4290 <- getRegister v_2536;
      v_4291 <- getRegister v_2535;
      v_4292 <- eval (bv_and v_4290 v_4291);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4292 24 32));
      setRegister sf (isBitSet v_4292 0);
      setRegister zf (zeroFlag v_4292);
      pure ()
    pat_end;
    pattern fun (v_2520 : imm int) (v_2519 : Mem) => do
      v_8743 <- evaluateAddress v_2519;
      v_8744 <- load v_8743 4;
      v_8746 <- eval (bv_and v_8744 (handleImmediateWithSignExtend v_2520 32 32));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8746 24 32));
      setRegister sf (isBitSet v_8746 0);
      setRegister zf (zeroFlag v_8746);
      pure ()
    pat_end;
    pattern fun (v_2526 : reg (bv 32)) (v_2523 : Mem) => do
      v_8757 <- evaluateAddress v_2523;
      v_8758 <- load v_8757 4;
      v_8759 <- getRegister v_2526;
      v_8760 <- eval (bv_and v_8758 v_8759);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8760 24 32));
      setRegister sf (isBitSet v_8760 0);
      setRegister zf (zeroFlag v_8760);
      pure ()
    pat_end
