def andnl1 : instruction :=
  definst "andnl" $ do
    pattern fun (v_2847 : reg (bv 32)) (v_2848 : reg (bv 32)) (v_2849 : reg (bv 32)) => do
      v_5355 <- getRegister v_2848;
      v_5357 <- getRegister v_2847;
      v_5358 <- eval (bv_and (bv_xor v_5355 (expression.bv_nat 32 4294967295)) v_5357);
      setRegister (lhs.of_reg v_2849) v_5358;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_5355 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5357 0));
      setRegister zf (zeroFlag v_5358);
      pure ()
    pat_end;
    pattern fun (v_2844 : Mem) (v_2842 : reg (bv 32)) (v_2843 : reg (bv 32)) => do
      v_9148 <- getRegister v_2842;
      v_9150 <- evaluateAddress v_2844;
      v_9151 <- load v_9150 4;
      v_9152 <- eval (bv_and (bv_xor v_9148 (expression.bv_nat 32 4294967295)) v_9151);
      setRegister (lhs.of_reg v_2843) v_9152;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_9148 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_9151 0));
      setRegister zf (zeroFlag v_9152);
      pure ()
    pat_end
