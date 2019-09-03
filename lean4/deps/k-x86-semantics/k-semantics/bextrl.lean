def bextrl1 : instruction :=
  definst "bextrl" $ do
    pattern fun (v_2907 : reg (bv 32)) (v_2908 : reg (bv 32)) (v_2909 : reg (bv 32)) => do
      v_5880 <- getRegister v_2908;
      v_5882 <- getRegister v_2907;
      v_5890 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5882 16 24)));
      v_5891 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_5890);
      v_5897 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_5880) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5882 24 32)))) 480 512) (bv_xor (extract (extract (shl v_5891 v_5890) 0 (bitwidthMInt v_5891)) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2909) v_5897;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5897);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2902 : reg (bv 32)) (v_2901 : Mem) (v_2903 : reg (bv 32)) => do
      v_9737 <- evaluateAddress v_2901;
      v_9738 <- load v_9737 4;
      v_9740 <- getRegister v_2902;
      v_9748 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9740 16 24)));
      v_9749 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_9748);
      v_9755 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_9738) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9740 24 32)))) 480 512) (bv_xor (extract (extract (shl v_9749 v_9748) 0 (bitwidthMInt v_9749)) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg v_2903) v_9755;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9755);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
