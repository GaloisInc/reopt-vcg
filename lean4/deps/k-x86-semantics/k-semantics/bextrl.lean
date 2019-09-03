def bextrl1 : instruction :=
  definst "bextrl" $ do
    pattern fun (v_2894 : reg (bv 32)) (v_2895 : reg (bv 32)) (v_2896 : reg (bv 32)) => do
      v_5717 <- getRegister v_2895;
      v_5719 <- getRegister v_2894;
      v_5727 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5719 16 24)));
      v_5728 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_5727);
      v_5732 <- eval (extract (extract (shl v_5728 v_5727) 0 (bitwidthMInt v_5728)) 480 512);
      v_5736 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_5717) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5719 24 32)))) 480 512) (bv_xor v_5732 (mi (bitwidthMInt v_5732) -1)));
      setRegister (lhs.of_reg v_2896) v_5736;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_5736);
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2889 : reg (bv 32)) (v_2888 : Mem) (v_2890 : reg (bv 32)) => do
      v_9441 <- evaluateAddress v_2888;
      v_9442 <- load v_9441 4;
      v_9444 <- getRegister v_2889;
      v_9452 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9444 16 24)));
      v_9453 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_9452);
      v_9457 <- eval (extract (extract (shl v_9453 v_9452) 0 (bitwidthMInt v_9453)) 480 512);
      v_9461 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_9442) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9444 24 32)))) 480 512) (bv_xor v_9457 (mi (bitwidthMInt v_9457) -1)));
      setRegister (lhs.of_reg v_2890) v_9461;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9461);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
