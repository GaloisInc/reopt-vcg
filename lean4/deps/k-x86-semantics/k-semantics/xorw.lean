def xorw1 : instruction :=
  definst "xorw" $ do
    pattern fun (v_3470 : imm int) (v_3469 : reg (bv 16)) => do
      v_8252 <- getRegister v_3469;
      v_8254 <- eval (bv_xor v_8252 (handleImmediateWithSignExtend v_3470 16 16));
      setRegister (lhs.of_reg v_3469) v_8254;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8254 8 16));
      setRegister sf (isBitSet v_8254 0);
      setRegister zf (zeroFlag v_8254);
      pure ()
    pat_end;
    pattern fun (v_3478 : reg (bv 16)) (v_3479 : reg (bv 16)) => do
      v_8270 <- getRegister v_3479;
      v_8271 <- getRegister v_3478;
      v_8272 <- eval (bv_xor v_8270 v_8271);
      setRegister (lhs.of_reg v_3479) v_8272;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8272 8 16));
      setRegister sf (isBitSet v_8272 0);
      setRegister zf (zeroFlag v_8272);
      pure ()
    pat_end;
    pattern fun (v_3473 : Mem) (v_3474 : reg (bv 16)) => do
      v_13591 <- getRegister v_3474;
      v_13592 <- evaluateAddress v_3473;
      v_13593 <- load v_13592 2;
      v_13594 <- eval (bv_xor v_13591 v_13593);
      setRegister (lhs.of_reg v_3474) v_13594;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13594 8 16));
      setRegister sf (isBitSet v_13594 0);
      setRegister zf (zeroFlag v_13594);
      pure ()
    pat_end;
    pattern fun (v_3461 : imm int) (v_3460 : Mem) => do
      v_13755 <- evaluateAddress v_3460;
      v_13756 <- load v_13755 2;
      v_13758 <- eval (bv_xor v_13756 (handleImmediateWithSignExtend v_3461 16 16));
      store v_13755 v_13758 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13758 8 16));
      setRegister sf (isBitSet v_13758 0);
      setRegister zf (zeroFlag v_13758);
      pure ()
    pat_end;
    pattern fun (v_3465 : reg (bv 16)) (v_3464 : Mem) => do
      v_13770 <- evaluateAddress v_3464;
      v_13771 <- load v_13770 2;
      v_13772 <- getRegister v_3465;
      v_13773 <- eval (bv_xor v_13771 v_13772);
      store v_13770 v_13773 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13773 8 16));
      setRegister sf (isBitSet v_13773 0);
      setRegister zf (zeroFlag v_13773);
      pure ()
    pat_end
