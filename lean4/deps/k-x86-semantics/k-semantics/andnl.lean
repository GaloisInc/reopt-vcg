def andnl1 : instruction :=
  definst "andnl" $ do
    pattern fun (v_2875 : reg (bv 32)) (v_2876 : reg (bv 32)) (v_2877 : reg (bv 32)) => do
      v_5236 <- getRegister v_2876;
      v_5238 <- getRegister v_2875;
      v_5239 <- eval (bv_and (bv_xor v_5236 (expression.bv_nat 32 4294967295)) v_5238);
      setRegister (lhs.of_reg v_2877) v_5239;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_5236 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5238 0));
      setRegister zf (zeroFlag v_5239);
      pure ()
    pat_end;
    pattern fun (v_2869 : Mem) (v_2870 : reg (bv 32)) (v_2871 : reg (bv 32)) => do
      v_8972 <- getRegister v_2870;
      v_8974 <- evaluateAddress v_2869;
      v_8975 <- load v_8974 4;
      v_8976 <- eval (bv_and (bv_xor v_8972 (expression.bv_nat 32 4294967295)) v_8975);
      setRegister (lhs.of_reg v_2871) v_8976;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_8972 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_8975 0));
      setRegister zf (zeroFlag v_8976);
      pure ()
    pat_end
