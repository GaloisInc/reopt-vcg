def lzcntw1 : instruction :=
  definst "lzcntw" $ do
    pattern fun (v_3133 : reg (bv 16)) (v_3134 : reg (bv 16)) => do
      v_5531 <- getRegister v_3133;
      v_5563 <- eval (mux (isBitSet v_5531 0) (expression.bv_nat 16 0) (mux (isBitSet v_5531 1) (expression.bv_nat 16 1) (mux (isBitSet v_5531 2) (expression.bv_nat 16 2) (mux (isBitSet v_5531 3) (expression.bv_nat 16 3) (mux (isBitSet v_5531 4) (expression.bv_nat 16 4) (mux (isBitSet v_5531 5) (expression.bv_nat 16 5) (mux (isBitSet v_5531 6) (expression.bv_nat 16 6) (mux (isBitSet v_5531 7) (expression.bv_nat 16 7) (mux (isBitSet v_5531 8) (expression.bv_nat 16 8) (mux (isBitSet v_5531 9) (expression.bv_nat 16 9) (mux (isBitSet v_5531 10) (expression.bv_nat 16 10) (mux (isBitSet v_5531 11) (expression.bv_nat 16 11) (mux (isBitSet v_5531 12) (expression.bv_nat 16 12) (mux (isBitSet v_5531 13) (expression.bv_nat 16 13) (mux (isBitSet v_5531 14) (expression.bv_nat 16 14) (mux (isBitSet v_5531 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3134) v_5563;
      setRegister af undef;
      setRegister cf (eq v_5563 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5563);
      pure ()
    pat_end;
    pattern fun (v_3129 : Mem) (v_3130 : reg (bv 16)) => do
      v_8789 <- evaluateAddress v_3129;
      v_8790 <- load v_8789 2;
      v_8822 <- eval (mux (isBitSet v_8790 0) (expression.bv_nat 16 0) (mux (isBitSet v_8790 1) (expression.bv_nat 16 1) (mux (isBitSet v_8790 2) (expression.bv_nat 16 2) (mux (isBitSet v_8790 3) (expression.bv_nat 16 3) (mux (isBitSet v_8790 4) (expression.bv_nat 16 4) (mux (isBitSet v_8790 5) (expression.bv_nat 16 5) (mux (isBitSet v_8790 6) (expression.bv_nat 16 6) (mux (isBitSet v_8790 7) (expression.bv_nat 16 7) (mux (isBitSet v_8790 8) (expression.bv_nat 16 8) (mux (isBitSet v_8790 9) (expression.bv_nat 16 9) (mux (isBitSet v_8790 10) (expression.bv_nat 16 10) (mux (isBitSet v_8790 11) (expression.bv_nat 16 11) (mux (isBitSet v_8790 12) (expression.bv_nat 16 12) (mux (isBitSet v_8790 13) (expression.bv_nat 16 13) (mux (isBitSet v_8790 14) (expression.bv_nat 16 14) (mux (isBitSet v_8790 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3130) v_8822;
      setRegister af undef;
      setRegister cf (eq v_8822 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_8822);
      pure ()
    pat_end
