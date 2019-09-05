def testw1 : instruction :=
  definst "testw" $ do
    pattern fun (v_2546 : imm int) (v_2548 : reg (bv 16)) => do
      v_4478 <- getRegister v_2548;
      v_4480 <- eval (bv_and v_4478 (handleImmediateWithSignExtend v_2546 16 16));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4480 8 16));
      setRegister sf (isBitSet v_4480 0);
      setRegister zf (zeroFlag v_4480);
      pure ()
    pat_end;
    pattern fun (v_2552 : reg (bv 16)) (v_2553 : reg (bv 16)) => do
      v_4491 <- getRegister v_2553;
      v_4492 <- getRegister v_2552;
      v_4493 <- eval (bv_and v_4491 v_4492);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4493 8 16));
      setRegister sf (isBitSet v_4493 0);
      setRegister zf (zeroFlag v_4493);
      pure ()
    pat_end;
    pattern fun (v_2539 : imm int) (v_2538 : Mem) => do
      v_8816 <- evaluateAddress v_2538;
      v_8817 <- load v_8816 2;
      v_8819 <- eval (bv_and v_8817 (handleImmediateWithSignExtend v_2539 16 16));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8819 8 16));
      setRegister sf (isBitSet v_8819 0);
      setRegister zf (zeroFlag v_8819);
      pure ()
    pat_end;
    pattern fun (v_2543 : reg (bv 16)) (v_2542 : Mem) => do
      v_8830 <- evaluateAddress v_2542;
      v_8831 <- load v_8830 2;
      v_8832 <- getRegister v_2543;
      v_8833 <- eval (bv_and v_8831 v_8832);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8833 8 16));
      setRegister sf (isBitSet v_8833 0);
      setRegister zf (zeroFlag v_8833);
      pure ()
    pat_end
