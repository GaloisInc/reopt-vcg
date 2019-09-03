def bextrq1 : instruction :=
  definst "bextrq" $ do
    pattern fun (v_2905 : reg (bv 64)) (v_2906 : reg (bv 64)) (v_2907 : reg (bv 64)) => do
      v_5750 <- getRegister v_2906;
      v_5752 <- getRegister v_2905;
      v_5760 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5752 48 56)));
      v_5761 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_5760);
      v_5765 <- eval (extract (extract (shl v_5761 v_5760) 0 (bitwidthMInt v_5761)) 448 512);
      v_5769 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_5750) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_5752 56 64)))) 448 512) (bv_xor v_5765 (mi (bitwidthMInt v_5765) -1)));
      setRegister (lhs.of_reg v_2907) v_5769;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5769);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2900 : reg (bv 64)) (v_2899 : Mem) (v_2901 : reg (bv 64)) => do
      v_9470 <- evaluateAddress v_2899;
      v_9471 <- load v_9470 8;
      v_9473 <- getRegister v_2900;
      v_9481 <- eval (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9473 48 56)));
      v_9482 <- eval (lshr (expression.bv_nat 512 18446744073709551615) v_9481);
      v_9486 <- eval (extract (extract (shl v_9482 v_9481) 0 (bitwidthMInt v_9482)) 448 512);
      v_9490 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_9471) (uvalueMInt (concat (expression.bv_nat 504 0) (extract v_9473 56 64)))) 448 512) (bv_xor v_9486 (mi (bitwidthMInt v_9486) -1)));
      setRegister (lhs.of_reg v_2901) v_9490;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9490);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
