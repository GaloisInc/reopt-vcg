def xorw1 : instruction :=
  definst "xorw" $ do
    pattern fun (v_3495 : imm int) (v_3497 : reg (bv 16)) => do
      v_8279 <- getRegister v_3497;
      v_8281 <- eval (bv_xor v_8279 (handleImmediateWithSignExtend v_3495 16 16));
      setRegister (lhs.of_reg v_3497) v_8281;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8281 8 16));
      setRegister sf (isBitSet v_8281 0);
      setRegister zf (zeroFlag v_8281);
      pure ()
    pat_end;
    pattern fun (v_3505 : reg (bv 16)) (v_3506 : reg (bv 16)) => do
      v_8297 <- getRegister v_3506;
      v_8298 <- getRegister v_3505;
      v_8299 <- eval (bv_xor v_8297 v_8298);
      setRegister (lhs.of_reg v_3506) v_8299;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8299 8 16));
      setRegister sf (isBitSet v_8299 0);
      setRegister zf (zeroFlag v_8299);
      pure ()
    pat_end;
    pattern fun (v_3500 : Mem) (v_3501 : reg (bv 16)) => do
      v_13618 <- getRegister v_3501;
      v_13619 <- evaluateAddress v_3500;
      v_13620 <- load v_13619 2;
      v_13621 <- eval (bv_xor v_13618 v_13620);
      setRegister (lhs.of_reg v_3501) v_13621;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13621 8 16));
      setRegister sf (isBitSet v_13621 0);
      setRegister zf (zeroFlag v_13621);
      pure ()
    pat_end;
    pattern fun (v_3487 : imm int) (v_3488 : Mem) => do
      v_13782 <- evaluateAddress v_3488;
      v_13783 <- load v_13782 2;
      v_13785 <- eval (bv_xor v_13783 (handleImmediateWithSignExtend v_3487 16 16));
      store v_13782 v_13785 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13785 8 16));
      setRegister sf (isBitSet v_13785 0);
      setRegister zf (zeroFlag v_13785);
      pure ()
    pat_end;
    pattern fun (v_3492 : reg (bv 16)) (v_3491 : Mem) => do
      v_13797 <- evaluateAddress v_3491;
      v_13798 <- load v_13797 2;
      v_13799 <- getRegister v_3492;
      v_13800 <- eval (bv_xor v_13798 v_13799);
      store v_13797 v_13800 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13800 8 16));
      setRegister sf (isBitSet v_13800 0);
      setRegister zf (zeroFlag v_13800);
      pure ()
    pat_end
