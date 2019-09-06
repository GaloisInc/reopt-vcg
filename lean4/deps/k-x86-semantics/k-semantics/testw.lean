def testw1 : instruction :=
  definst "testw" $ do
    pattern fun (v_2571 : imm int) (v_2573 : reg (bv 16)) => do
      v_4505 <- getRegister v_2573;
      v_4507 <- eval (bv_and v_4505 (handleImmediateWithSignExtend v_2571 16 16));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4507 8 16));
      setRegister sf (isBitSet v_4507 0);
      setRegister zf (zeroFlag v_4507);
      pure ()
    pat_end;
    pattern fun (v_2577 : reg (bv 16)) (v_2578 : reg (bv 16)) => do
      v_4518 <- getRegister v_2578;
      v_4519 <- getRegister v_2577;
      v_4520 <- eval (bv_and v_4518 v_4519);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4520 8 16));
      setRegister sf (isBitSet v_4520 0);
      setRegister zf (zeroFlag v_4520);
      pure ()
    pat_end;
    pattern fun (v_2564 : imm int) (v_2563 : Mem) => do
      v_8843 <- evaluateAddress v_2563;
      v_8844 <- load v_8843 2;
      v_8846 <- eval (bv_and v_8844 (handleImmediateWithSignExtend v_2564 16 16));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8846 8 16));
      setRegister sf (isBitSet v_8846 0);
      setRegister zf (zeroFlag v_8846);
      pure ()
    pat_end;
    pattern fun (v_2568 : reg (bv 16)) (v_2567 : Mem) => do
      v_8857 <- evaluateAddress v_2567;
      v_8858 <- load v_8857 2;
      v_8859 <- getRegister v_2568;
      v_8860 <- eval (bv_and v_8858 v_8859);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8860 8 16));
      setRegister sf (isBitSet v_8860 0);
      setRegister zf (zeroFlag v_8860);
      pure ()
    pat_end
