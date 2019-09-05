def orl1 : instruction :=
  definst "orl" $ do
    pattern fun (v_3022 : imm int) (v_3024 : reg (bv 32)) => do
      v_4779 <- getRegister v_3024;
      v_4781 <- eval (bv_or v_4779 (handleImmediateWithSignExtend v_3022 32 32));
      setRegister (lhs.of_reg v_3024) v_4781;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4781 24 32));
      setRegister sf (isBitSet v_4781 0);
      setRegister zf (zeroFlag v_4781);
      pure ()
    pat_end;
    pattern fun (v_3032 : reg (bv 32)) (v_3033 : reg (bv 32)) => do
      v_4797 <- getRegister v_3033;
      v_4798 <- getRegister v_3032;
      v_4799 <- eval (bv_or v_4797 v_4798);
      setRegister (lhs.of_reg v_3033) v_4799;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4799 24 32));
      setRegister sf (isBitSet v_4799 0);
      setRegister zf (zeroFlag v_4799);
      pure ()
    pat_end;
    pattern fun (v_3027 : Mem) (v_3028 : reg (bv 32)) => do
      v_8972 <- getRegister v_3028;
      v_8973 <- evaluateAddress v_3027;
      v_8974 <- load v_8973 4;
      v_8975 <- eval (bv_or v_8972 v_8974);
      setRegister (lhs.of_reg v_3028) v_8975;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8975 24 32));
      setRegister sf (isBitSet v_8975 0);
      setRegister zf (zeroFlag v_8975);
      pure ()
    pat_end;
    pattern fun (v_3015 : imm int) (v_3014 : Mem) => do
      v_10846 <- evaluateAddress v_3014;
      v_10847 <- load v_10846 4;
      v_10849 <- eval (bv_or v_10847 (handleImmediateWithSignExtend v_3015 32 32));
      store v_10846 v_10849 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10849 24 32));
      setRegister sf (isBitSet v_10849 0);
      setRegister zf (zeroFlag v_10849);
      pure ()
    pat_end;
    pattern fun (v_3019 : reg (bv 32)) (v_3018 : Mem) => do
      v_10861 <- evaluateAddress v_3018;
      v_10862 <- load v_10861 4;
      v_10863 <- getRegister v_3019;
      v_10864 <- eval (bv_or v_10862 v_10863);
      store v_10861 v_10864 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10864 24 32));
      setRegister sf (isBitSet v_10864 0);
      setRegister zf (zeroFlag v_10864);
      pure ()
    pat_end
