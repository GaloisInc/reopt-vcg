def bextrq1 : instruction :=
  definst "bextrq" $ do
    pattern fun (v_2918 : reg (bv 64)) (v_2919 : reg (bv 64)) (v_2920 : reg (bv 64)) => do
      v_5911 <- getRegister v_2919;
      v_5913 <- getRegister v_2918;
      v_5921 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5913 48 56)));
      v_5922 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_5921);
      v_5928 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_5911) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5913 56 64)))) 448 512) (bv_xor (extract (extract (shl v_5922 v_5921) 0 (bitwidthMInt v_5922)) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2920) v_5928;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5928);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2913 : reg (bv 64)) (v_2912 : Mem) (v_2914 : reg (bv 64)) => do
      v_9764 <- evaluateAddress v_2912;
      v_9765 <- load v_9764 8;
      v_9767 <- getRegister v_2913;
      v_9775 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9767 48 56)));
      v_9776 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_9775);
      v_9782 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_9765) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9767 56 64)))) 448 512) (bv_xor (extract (extract (shl v_9776 v_9775) 0 (bitwidthMInt v_9776)) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2914) v_9782;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9782);
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
