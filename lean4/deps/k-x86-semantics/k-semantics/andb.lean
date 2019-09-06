def andb1 : instruction :=
  definst "andb" $ do
    pattern fun (v_2822 : imm int) (v_2825 : reg (bv 8)) => do
      v_5085 <- getRegister v_2825;
      v_5087 <- eval (bv_and v_5085 (handleImmediateWithSignExtend v_2822 8 8));
      setRegister (lhs.of_reg v_2825) v_5087;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5087 0 8));
      setRegister sf (isBitSet v_5087 0);
      setRegister zf (zeroFlag v_5087);
      pure ()
    pat_end;
    pattern fun (v_2838 : reg (bv 8)) (v_2839 : reg (bv 8)) => do
      v_5117 <- getRegister v_2839;
      v_5118 <- getRegister v_2838;
      v_5119 <- eval (bv_and v_5117 v_5118);
      setRegister (lhs.of_reg v_2839) v_5119;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5119 0 8));
      setRegister sf (isBitSet v_5119 0);
      setRegister zf (zeroFlag v_5119);
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2830 : reg (bv 8)) => do
      v_8940 <- getRegister v_2830;
      v_8941 <- evaluateAddress v_2829;
      v_8942 <- load v_8941 1;
      v_8943 <- eval (bv_and v_8940 v_8942);
      setRegister (lhs.of_reg v_2830) v_8943;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8943 0 8));
      setRegister sf (isBitSet v_8943 0);
      setRegister zf (zeroFlag v_8943);
      pure ()
    pat_end;
    pattern fun (v_2791 : imm int) (v_2794 : Mem) => do
      v_10284 <- evaluateAddress v_2794;
      v_10285 <- load v_10284 1;
      v_10287 <- eval (bv_and v_10285 (handleImmediateWithSignExtend v_2791 8 8));
      store v_10284 v_10287 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10287 0 8));
      setRegister sf (isBitSet v_10287 0);
      setRegister zf (zeroFlag v_10287);
      pure ()
    pat_end;
    pattern fun (v_2802 : reg (bv 8)) (v_2801 : Mem) => do
      v_10314 <- evaluateAddress v_2801;
      v_10315 <- load v_10314 1;
      v_10316 <- getRegister v_2802;
      v_10317 <- eval (bv_and v_10315 v_10316);
      store v_10314 v_10317 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10317 0 8));
      setRegister sf (isBitSet v_10317 0);
      setRegister zf (zeroFlag v_10317);
      pure ()
    pat_end
