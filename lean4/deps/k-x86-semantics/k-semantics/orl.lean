def orl1 : instruction :=
  definst "orl" $ do
    pattern fun (v_3048 : imm int) (v_3049 : reg (bv 32)) => do
      v_4806 <- getRegister v_3049;
      v_4808 <- eval (bv_or v_4806 (handleImmediateWithSignExtend v_3048 32 32));
      setRegister (lhs.of_reg v_3049) v_4808;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4808 24 32));
      setRegister sf (isBitSet v_4808 0);
      setRegister zf (zeroFlag v_4808);
      pure ()
    pat_end;
    pattern fun (v_3057 : reg (bv 32)) (v_3058 : reg (bv 32)) => do
      v_4824 <- getRegister v_3058;
      v_4825 <- getRegister v_3057;
      v_4826 <- eval (bv_or v_4824 v_4825);
      setRegister (lhs.of_reg v_3058) v_4826;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4826 24 32));
      setRegister sf (isBitSet v_4826 0);
      setRegister zf (zeroFlag v_4826);
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3054 : reg (bv 32)) => do
      v_8999 <- getRegister v_3054;
      v_9000 <- evaluateAddress v_3053;
      v_9001 <- load v_9000 4;
      v_9002 <- eval (bv_or v_8999 v_9001);
      setRegister (lhs.of_reg v_3054) v_9002;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9002 24 32));
      setRegister sf (isBitSet v_9002 0);
      setRegister zf (zeroFlag v_9002);
      pure ()
    pat_end;
    pattern fun (v_3041 : imm int) (v_3040 : Mem) => do
      v_10873 <- evaluateAddress v_3040;
      v_10874 <- load v_10873 4;
      v_10876 <- eval (bv_or v_10874 (handleImmediateWithSignExtend v_3041 32 32));
      store v_10873 v_10876 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10876 24 32));
      setRegister sf (isBitSet v_10876 0);
      setRegister zf (zeroFlag v_10876);
      pure ()
    pat_end;
    pattern fun (v_3045 : reg (bv 32)) (v_3044 : Mem) => do
      v_10888 <- evaluateAddress v_3044;
      v_10889 <- load v_10888 4;
      v_10890 <- getRegister v_3045;
      v_10891 <- eval (bv_or v_10889 v_10890);
      store v_10888 v_10891 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10891 24 32));
      setRegister sf (isBitSet v_10891 0);
      setRegister zf (zeroFlag v_10891);
      pure ()
    pat_end
