def testb1 : instruction :=
  definst "testb" $ do
    pattern fun (v_2500 : imm int) (v_2502 : reg (bv 8)) => do
      v_4171 <- getRegister v_2502;
      v_4173 <- eval (bv_and v_4171 (handleImmediateWithSignExtend v_2500 8 8));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4173 0 8));
      setRegister sf (isBitSet v_4173 0);
      setRegister zf (zeroFlag v_4173);
      pure ()
    pat_end;
    pattern fun (v_2511 : reg (bv 8)) (v_2512 : reg (bv 8)) => do
      v_4197 <- getRegister v_2512;
      v_4198 <- getRegister v_2511;
      v_4199 <- eval (bv_and v_4197 v_4198);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4199 0 8));
      setRegister sf (isBitSet v_4199 0);
      setRegister zf (zeroFlag v_4199);
      pure ()
    pat_end;
    pattern fun (v_2473 : imm int) (v_2474 : Mem) => do
      v_8701 <- evaluateAddress v_2474;
      v_8702 <- load v_8701 1;
      v_8704 <- eval (bv_and v_8702 (handleImmediateWithSignExtend v_2473 8 8));
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8704 0 8));
      setRegister sf (isBitSet v_8704 0);
      setRegister zf (zeroFlag v_8704);
      pure ()
    pat_end;
    pattern fun (v_2482 : reg (bv 8)) (v_2481 : Mem) => do
      v_8729 <- evaluateAddress v_2481;
      v_8730 <- load v_8729 1;
      v_8731 <- getRegister v_2482;
      v_8732 <- eval (bv_and v_8730 v_8731);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8732 0 8));
      setRegister sf (isBitSet v_8732 0);
      setRegister zf (zeroFlag v_8732);
      pure ()
    pat_end
