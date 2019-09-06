def negq1 : instruction :=
  definst "negq" $ do
    pattern fun (v_2925 : reg (bv 64)) => do
      v_4492 <- getRegister v_2925;
      v_4494 <- eval (add (expression.bv_nat 64 1) (bv_xor v_4492 (expression.bv_nat 64 18446744073709551615)));
      v_4496 <- eval (isBitSet v_4494 0);
      setRegister (lhs.of_reg v_2925) v_4494;
      setRegister af (notBool_ (eq (isBitSet v_4492 59) (isBitSet v_4494 59)));
      setRegister cf (notBool_ (eq v_4492 (expression.bv_nat 64 0)));
      setRegister of (bit_and (isBitSet v_4492 0) v_4496);
      setRegister pf (parityFlag (extract v_4494 56 64));
      setRegister sf v_4496;
      setRegister zf (zeroFlag v_4494);
      pure ()
    pat_end;
    pattern fun (v_2922 : Mem) => do
      v_10766 <- evaluateAddress v_2922;
      v_10767 <- load v_10766 8;
      v_10769 <- eval (add (expression.bv_nat 64 1) (bv_xor v_10767 (expression.bv_nat 64 18446744073709551615)));
      store v_10766 v_10769 8;
      v_10772 <- eval (isBitSet v_10769 0);
      setRegister af (notBool_ (eq (isBitSet v_10767 59) (isBitSet v_10769 59)));
      setRegister cf (notBool_ (eq v_10767 (expression.bv_nat 64 0)));
      setRegister of (bit_and (isBitSet v_10767 0) v_10772);
      setRegister pf (parityFlag (extract v_10769 56 64));
      setRegister sf v_10772;
      setRegister zf (zeroFlag v_10769);
      pure ()
    pat_end
