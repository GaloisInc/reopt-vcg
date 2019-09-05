def lzcntw1 : instruction :=
  definst "lzcntw" $ do
    pattern fun (v_3107 : reg (bv 16)) (v_3108 : reg (bv 16)) => do
      v_5515 <- getRegister v_3107;
      v_5547 <- eval (mux (isBitSet v_5515 0) (expression.bv_nat 16 0) (mux (isBitSet v_5515 1) (expression.bv_nat 16 1) (mux (isBitSet v_5515 2) (expression.bv_nat 16 2) (mux (isBitSet v_5515 3) (expression.bv_nat 16 3) (mux (isBitSet v_5515 4) (expression.bv_nat 16 4) (mux (isBitSet v_5515 5) (expression.bv_nat 16 5) (mux (isBitSet v_5515 6) (expression.bv_nat 16 6) (mux (isBitSet v_5515 7) (expression.bv_nat 16 7) (mux (isBitSet v_5515 8) (expression.bv_nat 16 8) (mux (isBitSet v_5515 9) (expression.bv_nat 16 9) (mux (isBitSet v_5515 10) (expression.bv_nat 16 10) (mux (isBitSet v_5515 11) (expression.bv_nat 16 11) (mux (isBitSet v_5515 12) (expression.bv_nat 16 12) (mux (isBitSet v_5515 13) (expression.bv_nat 16 13) (mux (isBitSet v_5515 14) (expression.bv_nat 16 14) (mux (isBitSet v_5515 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3108) v_5547;
      setRegister af undef;
      setRegister cf (eq v_5547 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5547);
      pure ()
    pat_end;
    pattern fun (v_3102 : Mem) (v_3103 : reg (bv 16)) => do
      v_8779 <- evaluateAddress v_3102;
      v_8780 <- load v_8779 2;
      v_8812 <- eval (mux (isBitSet v_8780 0) (expression.bv_nat 16 0) (mux (isBitSet v_8780 1) (expression.bv_nat 16 1) (mux (isBitSet v_8780 2) (expression.bv_nat 16 2) (mux (isBitSet v_8780 3) (expression.bv_nat 16 3) (mux (isBitSet v_8780 4) (expression.bv_nat 16 4) (mux (isBitSet v_8780 5) (expression.bv_nat 16 5) (mux (isBitSet v_8780 6) (expression.bv_nat 16 6) (mux (isBitSet v_8780 7) (expression.bv_nat 16 7) (mux (isBitSet v_8780 8) (expression.bv_nat 16 8) (mux (isBitSet v_8780 9) (expression.bv_nat 16 9) (mux (isBitSet v_8780 10) (expression.bv_nat 16 10) (mux (isBitSet v_8780 11) (expression.bv_nat 16 11) (mux (isBitSet v_8780 12) (expression.bv_nat 16 12) (mux (isBitSet v_8780 13) (expression.bv_nat 16 13) (mux (isBitSet v_8780 14) (expression.bv_nat 16 14) (mux (isBitSet v_8780 15) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3103) v_8812;
      setRegister af undef;
      setRegister cf (eq v_8812 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_8812);
      pure ()
    pat_end
