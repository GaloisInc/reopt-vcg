def bextrl1 : instruction :=
  definst "bextrl" $ do
    pattern fun (v_2985 : reg (bv 32)) (v_2986 : reg (bv 32)) (v_2987 : reg (bv 32)) => do
      v_5558 <- getRegister v_2986;
      v_5560 <- getRegister v_2985;
      v_5566 <- eval (concat (expression.bv_nat 504 0) (extract v_5560 16 24));
      v_5572 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_5558) (concat (expression.bv_nat 504 0) (extract v_5560 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5566) v_5566) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2987) v_5572;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5572);
      pure ()
    pat_end;
    pattern fun (v_2980 : reg (bv 32)) (v_2979 : Mem) (v_2981 : reg (bv 32)) => do
      v_9064 <- evaluateAddress v_2979;
      v_9065 <- load v_9064 4;
      v_9067 <- getRegister v_2980;
      v_9073 <- eval (concat (expression.bv_nat 504 0) (extract v_9067 16 24));
      v_9079 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_9065) (concat (expression.bv_nat 504 0) (extract v_9067 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_9073) v_9073) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2981) v_9079;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9079);
      pure ()
    pat_end
