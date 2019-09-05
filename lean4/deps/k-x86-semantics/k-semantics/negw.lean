def negw1 : instruction :=
  definst "negw" $ do
    pattern fun (v_2907 : reg (bv 16)) => do
      v_4490 <- getRegister v_2907;
      v_4492 <- eval (add (expression.bv_nat 16 1) (bv_xor v_4490 (expression.bv_nat 16 65535)));
      v_4494 <- eval (isBitSet v_4492 0);
      setRegister (lhs.of_reg v_2907) v_4492;
      setRegister af (notBool_ (eq (isBitSet v_4490 11) (isBitSet v_4492 11)));
      setRegister cf (notBool_ (eq v_4490 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_4490 0) v_4494);
      setRegister pf (parityFlag (extract v_4492 8 16));
      setRegister sf v_4494;
      setRegister zf (zeroFlag v_4492);
      pure ()
    pat_end;
    pattern fun (v_2903 : Mem) => do
      v_10762 <- evaluateAddress v_2903;
      v_10763 <- load v_10762 2;
      v_10765 <- eval (add (expression.bv_nat 16 1) (bv_xor v_10763 (expression.bv_nat 16 65535)));
      store v_10762 v_10765 2;
      v_10768 <- eval (isBitSet v_10765 0);
      setRegister af (notBool_ (eq (isBitSet v_10763 11) (isBitSet v_10765 11)));
      setRegister cf (notBool_ (eq v_10763 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_10763 0) v_10768);
      setRegister pf (parityFlag (extract v_10765 8 16));
      setRegister sf v_10768;
      setRegister zf (zeroFlag v_10765);
      pure ()
    pat_end
