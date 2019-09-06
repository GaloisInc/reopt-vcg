def xorb1 : instruction :=
  definst "xorb" $ do
    pattern fun (v_3394 : imm int) (v_3395 : reg (bv 8)) => do
      v_7903 <- getRegister v_3395;
      v_7905 <- eval (bv_xor v_7903 (handleImmediateWithSignExtend v_3394 8 8));
      setRegister (lhs.of_reg v_3395) v_7905;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7905 0 8));
      setRegister sf (isBitSet v_7905 0);
      setRegister zf (zeroFlag v_7905);
      pure ()
    pat_end;
    pattern fun (v_3408 : reg (bv 8)) (v_3409 : reg (bv 8)) => do
      v_7935 <- getRegister v_3409;
      v_7936 <- getRegister v_3408;
      v_7937 <- eval (bv_xor v_7935 v_7936);
      setRegister (lhs.of_reg v_3409) v_7937;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7937 0 8));
      setRegister sf (isBitSet v_7937 0);
      setRegister zf (zeroFlag v_7937);
      pure ()
    pat_end;
    pattern fun (v_3399 : Mem) (v_3400 : reg (bv 8)) => do
      v_13557 <- getRegister v_3400;
      v_13558 <- evaluateAddress v_3399;
      v_13559 <- load v_13558 1;
      v_13560 <- eval (bv_xor v_13557 v_13559);
      setRegister (lhs.of_reg v_3400) v_13560;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13560 0 8));
      setRegister sf (isBitSet v_13560 0);
      setRegister zf (zeroFlag v_13560);
      pure ()
    pat_end;
    pattern fun (v_3363 : imm int) (v_3364 : Mem) => do
      v_13633 <- evaluateAddress v_3364;
      v_13634 <- load v_13633 1;
      v_13636 <- eval (bv_xor v_13634 (handleImmediateWithSignExtend v_3363 8 8));
      store v_13633 v_13636 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13636 0 8));
      setRegister sf (isBitSet v_13636 0);
      setRegister zf (zeroFlag v_13636);
      pure ()
    pat_end;
    pattern fun (v_3372 : reg (bv 8)) (v_3371 : Mem) => do
      v_13663 <- evaluateAddress v_3371;
      v_13664 <- load v_13663 1;
      v_13665 <- getRegister v_3372;
      v_13666 <- eval (bv_xor v_13664 v_13665);
      store v_13663 v_13666 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13666 0 8));
      setRegister sf (isBitSet v_13666 0);
      setRegister zf (zeroFlag v_13666);
      pure ()
    pat_end
