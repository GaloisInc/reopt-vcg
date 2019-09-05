def xorl1 : instruction :=
  definst "xorl" $ do
    pattern fun (v_3400 : imm int) (v_3399 : reg (bv 32)) => do
      v_7991 <- getRegister v_3399;
      v_7993 <- eval (bv_xor v_7991 (handleImmediateWithSignExtend v_3400 32 32));
      setRegister (lhs.of_reg v_3399) v_7993;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7993 24 32));
      setRegister sf (isBitSet v_7993 0);
      setRegister zf (zeroFlag v_7993);
      pure ()
    pat_end;
    pattern fun (v_3408 : reg (bv 32)) (v_3409 : reg (bv 32)) => do
      v_8009 <- getRegister v_3409;
      v_8010 <- getRegister v_3408;
      v_8011 <- eval (bv_xor v_8009 v_8010);
      setRegister (lhs.of_reg v_3409) v_8011;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8011 24 32));
      setRegister sf (isBitSet v_8011 0);
      setRegister zf (zeroFlag v_8011);
      pure ()
    pat_end;
    pattern fun (v_3403 : Mem) (v_3404 : reg (bv 32)) => do
      v_13547 <- getRegister v_3404;
      v_13548 <- evaluateAddress v_3403;
      v_13549 <- load v_13548 4;
      v_13550 <- eval (bv_xor v_13547 v_13549);
      setRegister (lhs.of_reg v_3404) v_13550;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13550 24 32));
      setRegister sf (isBitSet v_13550 0);
      setRegister zf (zeroFlag v_13550);
      pure ()
    pat_end;
    pattern fun (v_3391 : imm int) (v_3390 : Mem) => do
      v_13651 <- evaluateAddress v_3390;
      v_13652 <- load v_13651 4;
      v_13654 <- eval (bv_xor v_13652 (handleImmediateWithSignExtend v_3391 32 32));
      store v_13651 v_13654 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13654 24 32));
      setRegister sf (isBitSet v_13654 0);
      setRegister zf (zeroFlag v_13654);
      pure ()
    pat_end;
    pattern fun (v_3395 : reg (bv 32)) (v_3394 : Mem) => do
      v_13666 <- evaluateAddress v_3394;
      v_13667 <- load v_13666 4;
      v_13668 <- getRegister v_3395;
      v_13669 <- eval (bv_xor v_13667 v_13668);
      store v_13666 v_13669 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13669 24 32));
      setRegister sf (isBitSet v_13669 0);
      setRegister zf (zeroFlag v_13669);
      pure ()
    pat_end
