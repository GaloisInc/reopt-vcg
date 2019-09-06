def andw1 : instruction :=
  definst "andw" $ do
    pattern fun (v_2965 : imm int) (v_2966 : reg (bv 16)) => do
      v_5521 <- getRegister v_2966;
      v_5523 <- eval (bv_and v_5521 (handleImmediateWithSignExtend v_2965 16 16));
      setRegister (lhs.of_reg v_2966) v_5523;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5523 8 16));
      setRegister sf (isBitSet v_5523 0);
      setRegister zf (zeroFlag v_5523);
      pure ()
    pat_end;
    pattern fun (v_2974 : reg (bv 16)) (v_2975 : reg (bv 16)) => do
      v_5539 <- getRegister v_2975;
      v_5540 <- getRegister v_2974;
      v_5541 <- eval (bv_and v_5539 v_5540);
      setRegister (lhs.of_reg v_2975) v_5541;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5541 8 16));
      setRegister sf (isBitSet v_5541 0);
      setRegister zf (zeroFlag v_5541);
      pure ()
    pat_end;
    pattern fun (v_2970 : Mem) (v_2971 : reg (bv 16)) => do
      v_9049 <- getRegister v_2971;
      v_9050 <- evaluateAddress v_2970;
      v_9051 <- load v_9050 2;
      v_9052 <- eval (bv_and v_9049 v_9051);
      setRegister (lhs.of_reg v_2971) v_9052;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9052 8 16));
      setRegister sf (isBitSet v_9052 0);
      setRegister zf (zeroFlag v_9052);
      pure ()
    pat_end;
    pattern fun (v_2958 : imm int) (v_2957 : Mem) => do
      v_10433 <- evaluateAddress v_2957;
      v_10434 <- load v_10433 2;
      v_10436 <- eval (bv_and v_10434 (handleImmediateWithSignExtend v_2958 16 16));
      store v_10433 v_10436 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10436 8 16));
      setRegister sf (isBitSet v_10436 0);
      setRegister zf (zeroFlag v_10436);
      pure ()
    pat_end;
    pattern fun (v_2962 : reg (bv 16)) (v_2961 : Mem) => do
      v_10448 <- evaluateAddress v_2961;
      v_10449 <- load v_10448 2;
      v_10450 <- getRegister v_2962;
      v_10451 <- eval (bv_and v_10449 v_10450);
      store v_10448 v_10451 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10451 8 16));
      setRegister sf (isBitSet v_10451 0);
      setRegister zf (zeroFlag v_10451);
      pure ()
    pat_end
