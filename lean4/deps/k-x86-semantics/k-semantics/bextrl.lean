def bextrl1 : instruction :=
  definst "bextrl" $ do
    pattern fun (v_2957 : reg (bv 32)) (v_2958 : reg (bv 32)) (v_2959 : reg (bv 32)) => do
      v_5677 <- getRegister v_2958;
      v_5679 <- getRegister v_2957;
      v_5685 <- eval (concat (expression.bv_nat 504 0) (extract v_5679 16 24));
      v_5691 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_5677) (concat (expression.bv_nat 504 0) (extract v_5679 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5685) v_5685) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2959) v_5691;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5691);
      pure ()
    pat_end;
    pattern fun (v_2952 : reg (bv 32)) (v_2954 : Mem) (v_2953 : reg (bv 32)) => do
      v_9240 <- evaluateAddress v_2954;
      v_9241 <- load v_9240 4;
      v_9243 <- getRegister v_2952;
      v_9249 <- eval (concat (expression.bv_nat 504 0) (extract v_9243 16 24));
      v_9255 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_9241) (concat (expression.bv_nat 504 0) (extract v_9243 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_9249) v_9249) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2953) v_9255;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9255);
      pure ()
    pat_end
