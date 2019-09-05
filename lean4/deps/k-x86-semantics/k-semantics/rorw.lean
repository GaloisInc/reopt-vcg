def rorw1 : instruction :=
  definst "rorw" $ do
    pattern fun cl (v_2811 : reg (bv 16)) => do
      v_5384 <- getRegister rcx;
      v_5386 <- eval (bv_and (extract v_5384 56 64) (expression.bv_nat 8 31));
      v_5387 <- eval (eq v_5386 (expression.bv_nat 8 1));
      v_5388 <- getRegister v_2811;
      v_5390 <- eval (ror v_5388 (concat (expression.bv_nat 8 0) v_5386));
      v_5391 <- eval (isBitSet v_5390 0);
      v_5397 <- eval (eq v_5386 (expression.bv_nat 8 0));
      v_5398 <- eval (notBool_ v_5397);
      v_5400 <- getRegister of;
      v_5407 <- getRegister cf;
      setRegister (lhs.of_reg v_2811) v_5390;
      setRegister cf (bit_or (bit_and v_5398 v_5391) (bit_and v_5397 (eq v_5407 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5387 (notBool_ (eq v_5391 (isBitSet v_5390 1)))) (bit_and (notBool_ v_5387) (bit_or (bit_and v_5398 undef) (bit_and v_5397 (eq v_5400 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2818 : imm int) (v_2815 : reg (bv 16)) => do
      v_5415 <- eval (bv_and (handleImmediateWithSignExtend v_2818 8 8) (expression.bv_nat 8 31));
      v_5416 <- eval (eq v_5415 (expression.bv_nat 8 1));
      v_5417 <- getRegister v_2815;
      v_5419 <- eval (ror v_5417 (concat (expression.bv_nat 8 0) v_5415));
      v_5420 <- eval (isBitSet v_5419 0);
      v_5426 <- eval (eq v_5415 (expression.bv_nat 8 0));
      v_5427 <- eval (notBool_ v_5426);
      v_5429 <- getRegister of;
      v_5436 <- getRegister cf;
      setRegister (lhs.of_reg v_2815) v_5419;
      setRegister cf (bit_or (bit_and v_5427 v_5420) (bit_and v_5426 (eq v_5436 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5416 (notBool_ (eq v_5420 (isBitSet v_5419 1)))) (bit_and (notBool_ v_5416) (bit_or (bit_and v_5427 undef) (bit_and v_5426 (eq v_5429 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2803 : Mem) => do
      v_12776 <- evaluateAddress v_2803;
      v_12777 <- load v_12776 2;
      v_12778 <- getRegister rcx;
      v_12780 <- eval (bv_and (extract v_12778 56 64) (expression.bv_nat 8 31));
      v_12782 <- eval (ror v_12777 (concat (expression.bv_nat 8 0) v_12780));
      store v_12776 v_12782 2;
      v_12784 <- eval (eq v_12780 (expression.bv_nat 8 1));
      v_12785 <- eval (isBitSet v_12782 0);
      v_12791 <- eval (eq v_12780 (expression.bv_nat 8 0));
      v_12792 <- eval (notBool_ v_12791);
      v_12794 <- getRegister of;
      v_12801 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12792 v_12785) (bit_and v_12791 (eq v_12801 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12784 (notBool_ (eq v_12785 (isBitSet v_12782 1)))) (bit_and (notBool_ v_12784) (bit_or (bit_and v_12792 undef) (bit_and v_12791 (eq v_12794 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2806 : imm int) (v_2807 : Mem) => do
      v_12807 <- evaluateAddress v_2807;
      v_12808 <- load v_12807 2;
      v_12810 <- eval (bv_and (handleImmediateWithSignExtend v_2806 8 8) (expression.bv_nat 8 31));
      v_12812 <- eval (ror v_12808 (concat (expression.bv_nat 8 0) v_12810));
      store v_12807 v_12812 2;
      v_12814 <- eval (eq v_12810 (expression.bv_nat 8 1));
      v_12815 <- eval (isBitSet v_12812 0);
      v_12821 <- eval (eq v_12810 (expression.bv_nat 8 0));
      v_12822 <- eval (notBool_ v_12821);
      v_12824 <- getRegister of;
      v_12831 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12822 v_12815) (bit_and v_12821 (eq v_12831 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12814 (notBool_ (eq v_12815 (isBitSet v_12812 1)))) (bit_and (notBool_ v_12814) (bit_or (bit_and v_12822 undef) (bit_and v_12821 (eq v_12824 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
