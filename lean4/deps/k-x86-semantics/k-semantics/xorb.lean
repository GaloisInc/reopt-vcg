def xorb1 : instruction :=
  definst "xorb" $ do
    pattern fun (v_3369 : imm int) (v_3368 : reg (bv 8)) => do
      v_7876 <- getRegister v_3368;
      v_7878 <- eval (bv_xor v_7876 (handleImmediateWithSignExtend v_3369 8 8));
      setRegister (lhs.of_reg v_3368) v_7878;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7878 0 8));
      setRegister sf (isBitSet v_7878 0);
      setRegister zf (zeroFlag v_7878);
      pure ()
    pat_end;
    pattern fun (v_3382 : reg (bv 8)) (v_3383 : reg (bv 8)) => do
      v_7908 <- getRegister v_3383;
      v_7909 <- getRegister v_3382;
      v_7910 <- eval (bv_xor v_7908 v_7909);
      setRegister (lhs.of_reg v_3383) v_7910;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7910 0 8));
      setRegister sf (isBitSet v_7910 0);
      setRegister zf (zeroFlag v_7910);
      pure ()
    pat_end;
    pattern fun (v_3372 : Mem) (v_3373 : reg (bv 8)) => do
      v_13530 <- getRegister v_3373;
      v_13531 <- evaluateAddress v_3372;
      v_13532 <- load v_13531 1;
      v_13533 <- eval (bv_xor v_13530 v_13532);
      setRegister (lhs.of_reg v_3373) v_13533;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13533 0 8));
      setRegister sf (isBitSet v_13533 0);
      setRegister zf (zeroFlag v_13533);
      pure ()
    pat_end;
    pattern fun (v_3337 : imm int) (v_3336 : Mem) => do
      v_13606 <- evaluateAddress v_3336;
      v_13607 <- load v_13606 1;
      v_13609 <- eval (bv_xor v_13607 (handleImmediateWithSignExtend v_3337 8 8));
      store v_13606 v_13609 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13609 0 8));
      setRegister sf (isBitSet v_13609 0);
      setRegister zf (zeroFlag v_13609);
      pure ()
    pat_end;
    pattern fun (v_3345 : reg (bv 8)) (v_3344 : Mem) => do
      v_13636 <- evaluateAddress v_3344;
      v_13637 <- load v_13636 1;
      v_13638 <- getRegister v_3345;
      v_13639 <- eval (bv_xor v_13637 v_13638);
      store v_13636 v_13639 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13639 0 8));
      setRegister sf (isBitSet v_13639 0);
      setRegister zf (zeroFlag v_13639);
      pure ()
    pat_end
