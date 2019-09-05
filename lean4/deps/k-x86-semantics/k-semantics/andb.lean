def andb1 : instruction :=
  definst "andb" $ do
    pattern fun (v_2796 : imm int) (v_2799 : reg (bv 8)) => do
      v_5204 <- getRegister v_2799;
      v_5206 <- eval (bv_and v_5204 (handleImmediateWithSignExtend v_2796 8 8));
      setRegister (lhs.of_reg v_2799) v_5206;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5206 0 8));
      setRegister sf (isBitSet v_5206 0);
      setRegister zf (zeroFlag v_5206);
      pure ()
    pat_end;
    pattern fun (v_2812 : reg (bv 8)) (v_2813 : reg (bv 8)) => do
      v_5236 <- getRegister v_2813;
      v_5237 <- getRegister v_2812;
      v_5238 <- eval (bv_and v_5236 v_5237);
      setRegister (lhs.of_reg v_2813) v_5238;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5238 0 8));
      setRegister sf (isBitSet v_5238 0);
      setRegister zf (zeroFlag v_5238);
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2803 : reg (bv 8)) => do
      v_9116 <- getRegister v_2803;
      v_9117 <- evaluateAddress v_2802;
      v_9118 <- load v_9117 1;
      v_9119 <- eval (bv_and v_9116 v_9118);
      setRegister (lhs.of_reg v_2803) v_9119;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9119 0 8));
      setRegister sf (isBitSet v_9119 0);
      setRegister zf (zeroFlag v_9119);
      pure ()
    pat_end;
    pattern fun (v_2765 : imm int) (v_2767 : Mem) => do
      v_10560 <- evaluateAddress v_2767;
      v_10561 <- load v_10560 1;
      v_10563 <- eval (bv_and v_10561 (handleImmediateWithSignExtend v_2765 8 8));
      store v_10560 v_10563 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10563 0 8));
      setRegister sf (isBitSet v_10563 0);
      setRegister zf (zeroFlag v_10563);
      pure ()
    pat_end;
    pattern fun (v_2775 : reg (bv 8)) (v_2774 : Mem) => do
      v_10590 <- evaluateAddress v_2774;
      v_10591 <- load v_10590 1;
      v_10592 <- getRegister v_2775;
      v_10593 <- eval (bv_and v_10591 v_10592);
      store v_10590 v_10593 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10593 0 8));
      setRegister sf (isBitSet v_10593 0);
      setRegister zf (zeroFlag v_10593);
      pure ()
    pat_end
