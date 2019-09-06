def orw1 : instruction :=
  definst "orw" $ do
    pattern fun (v_3118 : imm int) (v_3119 : reg (bv 16)) => do
      v_5066 <- getRegister v_3119;
      v_5068 <- eval (bv_or v_5066 (handleImmediateWithSignExtend v_3118 16 16));
      setRegister (lhs.of_reg v_3119) v_5068;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5068 8 16));
      setRegister sf (isBitSet v_5068 0);
      setRegister zf (zeroFlag v_5068);
      pure ()
    pat_end;
    pattern fun (v_3127 : reg (bv 16)) (v_3128 : reg (bv 16)) => do
      v_5084 <- getRegister v_3128;
      v_5085 <- getRegister v_3127;
      v_5086 <- eval (bv_or v_5084 v_5085);
      setRegister (lhs.of_reg v_3128) v_5086;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5086 8 16));
      setRegister sf (isBitSet v_5086 0);
      setRegister zf (zeroFlag v_5086);
      pure ()
    pat_end;
    pattern fun (v_3123 : Mem) (v_3124 : reg (bv 16)) => do
      v_9043 <- getRegister v_3124;
      v_9044 <- evaluateAddress v_3123;
      v_9045 <- load v_9044 2;
      v_9046 <- eval (bv_or v_9043 v_9045);
      setRegister (lhs.of_reg v_3124) v_9046;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9046 8 16));
      setRegister sf (isBitSet v_9046 0);
      setRegister zf (zeroFlag v_9046);
      pure ()
    pat_end;
    pattern fun (v_3111 : imm int) (v_3110 : Mem) => do
      v_10977 <- evaluateAddress v_3110;
      v_10978 <- load v_10977 2;
      v_10980 <- eval (bv_or v_10978 (handleImmediateWithSignExtend v_3111 16 16));
      store v_10977 v_10980 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10980 8 16));
      setRegister sf (isBitSet v_10980 0);
      setRegister zf (zeroFlag v_10980);
      pure ()
    pat_end;
    pattern fun (v_3115 : reg (bv 16)) (v_3114 : Mem) => do
      v_10992 <- evaluateAddress v_3114;
      v_10993 <- load v_10992 2;
      v_10994 <- getRegister v_3115;
      v_10995 <- eval (bv_or v_10993 v_10994);
      store v_10992 v_10995 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10995 8 16));
      setRegister sf (isBitSet v_10995 0);
      setRegister zf (zeroFlag v_10995);
      pure ()
    pat_end
