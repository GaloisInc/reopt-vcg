def bextrq1 : instruction :=
  definst "bextrq" $ do
    pattern fun (v_2969 : reg (bv 64)) (v_2970 : reg (bv 64)) (v_2971 : reg (bv 64)) => do
      v_5705 <- getRegister v_2970;
      v_5707 <- getRegister v_2969;
      v_5713 <- eval (concat (expression.bv_nat 504 0) (extract v_5707 48 56));
      v_5719 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_5705) (concat (expression.bv_nat 504 0) (extract v_5707 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5713) v_5713) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2971) v_5719;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5719);
      pure ()
    pat_end;
    pattern fun (v_2964 : reg (bv 64)) (v_2963 : Mem) (v_2965 : reg (bv 64)) => do
      v_9264 <- evaluateAddress v_2963;
      v_9265 <- load v_9264 8;
      v_9267 <- getRegister v_2964;
      v_9273 <- eval (concat (expression.bv_nat 504 0) (extract v_9267 48 56));
      v_9279 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_9265) (concat (expression.bv_nat 504 0) (extract v_9267 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_9273) v_9273) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2965) v_9279;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9279);
      pure ()
    pat_end
