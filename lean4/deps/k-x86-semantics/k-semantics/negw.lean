def negw1 : instruction :=
  definst "negw" $ do
    pattern fun (v_2932 : reg (bv 16)) => do
      v_4517 <- getRegister v_2932;
      v_4519 <- eval (add (expression.bv_nat 16 1) (bv_xor v_4517 (expression.bv_nat 16 65535)));
      v_4521 <- eval (isBitSet v_4519 0);
      setRegister (lhs.of_reg v_2932) v_4519;
      setRegister af (notBool_ (eq (isBitSet v_4517 11) (isBitSet v_4519 11)));
      setRegister cf (notBool_ (eq v_4517 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_4517 0) v_4521);
      setRegister pf (parityFlag (extract v_4519 8 16));
      setRegister sf v_4521;
      setRegister zf (zeroFlag v_4519);
      pure ()
    pat_end;
    pattern fun (v_2929 : Mem) => do
      v_10789 <- evaluateAddress v_2929;
      v_10790 <- load v_10789 2;
      v_10792 <- eval (add (expression.bv_nat 16 1) (bv_xor v_10790 (expression.bv_nat 16 65535)));
      store v_10789 v_10792 2;
      v_10795 <- eval (isBitSet v_10792 0);
      setRegister af (notBool_ (eq (isBitSet v_10790 11) (isBitSet v_10792 11)));
      setRegister cf (notBool_ (eq v_10790 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_10790 0) v_10795);
      setRegister pf (parityFlag (extract v_10792 8 16));
      setRegister sf v_10795;
      setRegister zf (zeroFlag v_10792);
      pure ()
    pat_end
