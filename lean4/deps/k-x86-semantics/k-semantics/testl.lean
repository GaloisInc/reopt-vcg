def testl1 : instruction :=
  definst "testl" $ do
    pattern fun (v_2502 : imm int) (v_2504 : reg (bv 32)) => do
      v_4250 <- getRegister v_2504;
      v_4252 <- eval (bv_and v_4250 (handleImmediateWithSignExtend v_2502 32 32));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4252 24 32));
      setRegister sf (isBitSet v_4252 0);
      setRegister zf (zeroFlag v_4252);
      pure ()
    pat_end;
    pattern fun (v_2508 : reg (bv 32)) (v_2509 : reg (bv 32)) => do
      v_4263 <- getRegister v_2509;
      v_4264 <- getRegister v_2508;
      v_4265 <- eval (bv_and v_4263 v_4264);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4265 24 32));
      setRegister sf (isBitSet v_4265 0);
      setRegister zf (zeroFlag v_4265);
      pure ()
    pat_end;
    pattern fun (v_2495 : imm int) (v_2494 : Mem) => do
      v_8716 <- evaluateAddress v_2494;
      v_8717 <- load v_8716 4;
      v_8719 <- eval (bv_and v_8717 (handleImmediateWithSignExtend v_2495 32 32));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8719 24 32));
      setRegister sf (isBitSet v_8719 0);
      setRegister zf (zeroFlag v_8719);
      pure ()
    pat_end;
    pattern fun (v_2499 : reg (bv 32)) (v_2498 : Mem) => do
      v_8730 <- evaluateAddress v_2498;
      v_8731 <- load v_8730 4;
      v_8732 <- getRegister v_2499;
      v_8733 <- eval (bv_and v_8731 v_8732);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8733 24 32));
      setRegister sf (isBitSet v_8733 0);
      setRegister zf (zeroFlag v_8733);
      pure ()
    pat_end
