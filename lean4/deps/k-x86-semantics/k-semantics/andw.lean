def andw1 : instruction :=
  definst "andw" $ do
    pattern fun (v_2939 : imm int) (v_2936 : reg (bv 16)) => do
      v_5640 <- getRegister v_2936;
      v_5642 <- eval (bv_and v_5640 (handleImmediateWithSignExtend v_2939 16 16));
      setRegister (lhs.of_reg v_2936) v_5642;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5642 8 16));
      setRegister sf (isBitSet v_5642 0);
      setRegister zf (zeroFlag v_5642);
      pure ()
    pat_end;
    pattern fun (v_2945 : reg (bv 16)) (v_2946 : reg (bv 16)) => do
      v_5658 <- getRegister v_2946;
      v_5659 <- getRegister v_2945;
      v_5660 <- eval (bv_and v_5658 v_5659);
      setRegister (lhs.of_reg v_2946) v_5660;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5660 8 16));
      setRegister sf (isBitSet v_5660 0);
      setRegister zf (zeroFlag v_5660);
      pure ()
    pat_end;
    pattern fun (v_2944 : Mem) (v_2941 : reg (bv 16)) => do
      v_9225 <- getRegister v_2941;
      v_9226 <- evaluateAddress v_2944;
      v_9227 <- load v_9226 2;
      v_9228 <- eval (bv_and v_9225 v_9227);
      setRegister (lhs.of_reg v_2941) v_9228;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9228 8 16));
      setRegister sf (isBitSet v_9228 0);
      setRegister zf (zeroFlag v_9228);
      pure ()
    pat_end;
    pattern fun (v_2930 : imm int) (v_2931 : Mem) => do
      v_10709 <- evaluateAddress v_2931;
      v_10710 <- load v_10709 2;
      v_10712 <- eval (bv_and v_10710 (handleImmediateWithSignExtend v_2930 16 16));
      store v_10709 v_10712 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10712 8 16));
      setRegister sf (isBitSet v_10712 0);
      setRegister zf (zeroFlag v_10712);
      pure ()
    pat_end;
    pattern fun (v_2932 : reg (bv 16)) (v_2935 : Mem) => do
      v_10724 <- evaluateAddress v_2935;
      v_10725 <- load v_10724 2;
      v_10726 <- getRegister v_2932;
      v_10727 <- eval (bv_and v_10725 v_10726);
      store v_10724 v_10727 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10727 8 16));
      setRegister sf (isBitSet v_10727 0);
      setRegister zf (zeroFlag v_10727);
      pure ()
    pat_end
