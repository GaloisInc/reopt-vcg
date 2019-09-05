def testb1 : instruction :=
  definst "testb" $ do
    pattern fun (v_2475 : imm int) (v_2477 : reg (bv 8)) => do
      v_4144 <- getRegister v_2477;
      v_4146 <- eval (bv_and v_4144 (handleImmediateWithSignExtend v_2475 8 8));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4146 0 8));
      setRegister sf (isBitSet v_4146 0);
      setRegister zf (zeroFlag v_4146);
      pure ()
    pat_end;
    pattern fun (v_2486 : reg (bv 8)) (v_2487 : reg (bv 8)) => do
      v_4170 <- getRegister v_2487;
      v_4171 <- getRegister v_2486;
      v_4172 <- eval (bv_and v_4170 v_4171);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4172 0 8));
      setRegister sf (isBitSet v_4172 0);
      setRegister zf (zeroFlag v_4172);
      pure ()
    pat_end;
    pattern fun (v_2448 : imm int) (v_2449 : Mem) => do
      v_8674 <- evaluateAddress v_2449;
      v_8675 <- load v_8674 1;
      v_8677 <- eval (bv_and v_8675 (handleImmediateWithSignExtend v_2448 8 8));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8677 0 8));
      setRegister sf (isBitSet v_8677 0);
      setRegister zf (zeroFlag v_8677);
      pure ()
    pat_end;
    pattern fun (v_2457 : reg (bv 8)) (v_2456 : Mem) => do
      v_8702 <- evaluateAddress v_2456;
      v_8703 <- load v_8702 1;
      v_8704 <- getRegister v_2457;
      v_8705 <- eval (bv_and v_8703 v_8704);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8705 0 8));
      setRegister sf (isBitSet v_8705 0);
      setRegister zf (zeroFlag v_8705);
      pure ()
    pat_end
