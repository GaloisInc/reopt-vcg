def tzcntw1 : instruction :=
  definst "tzcntw" $ do
    pattern fun (v_2570 : reg (bv 16)) (v_2571 : reg (bv 16)) => do
      v_4650 <- getRegister v_2570;
      v_4682 <- eval (mux (isBitSet v_4650 15) (expression.bv_nat 16 0) (mux (isBitSet v_4650 14) (expression.bv_nat 16 1) (mux (isBitSet v_4650 13) (expression.bv_nat 16 2) (mux (isBitSet v_4650 12) (expression.bv_nat 16 3) (mux (isBitSet v_4650 11) (expression.bv_nat 16 4) (mux (isBitSet v_4650 10) (expression.bv_nat 16 5) (mux (isBitSet v_4650 9) (expression.bv_nat 16 6) (mux (isBitSet v_4650 8) (expression.bv_nat 16 7) (mux (isBitSet v_4650 7) (expression.bv_nat 16 8) (mux (isBitSet v_4650 6) (expression.bv_nat 16 9) (mux (isBitSet v_4650 5) (expression.bv_nat 16 10) (mux (isBitSet v_4650 4) (expression.bv_nat 16 11) (mux (isBitSet v_4650 3) (expression.bv_nat 16 12) (mux (isBitSet v_4650 2) (expression.bv_nat 16 13) (mux (isBitSet v_4650 1) (expression.bv_nat 16 14) (mux (isBitSet v_4650 0) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2571) v_4682;
      setRegister af undef;
      setRegister cf (eq v_4682 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_4682);
      pure ()
    pat_end;
    pattern fun (v_2565 : Mem) (v_2566 : reg (bv 16)) => do
      v_8983 <- evaluateAddress v_2565;
      v_8984 <- load v_8983 2;
      v_9016 <- eval (mux (isBitSet v_8984 15) (expression.bv_nat 16 0) (mux (isBitSet v_8984 14) (expression.bv_nat 16 1) (mux (isBitSet v_8984 13) (expression.bv_nat 16 2) (mux (isBitSet v_8984 12) (expression.bv_nat 16 3) (mux (isBitSet v_8984 11) (expression.bv_nat 16 4) (mux (isBitSet v_8984 10) (expression.bv_nat 16 5) (mux (isBitSet v_8984 9) (expression.bv_nat 16 6) (mux (isBitSet v_8984 8) (expression.bv_nat 16 7) (mux (isBitSet v_8984 7) (expression.bv_nat 16 8) (mux (isBitSet v_8984 6) (expression.bv_nat 16 9) (mux (isBitSet v_8984 5) (expression.bv_nat 16 10) (mux (isBitSet v_8984 4) (expression.bv_nat 16 11) (mux (isBitSet v_8984 3) (expression.bv_nat 16 12) (mux (isBitSet v_8984 2) (expression.bv_nat 16 13) (mux (isBitSet v_8984 1) (expression.bv_nat 16 14) (mux (isBitSet v_8984 0) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2566) v_9016;
      setRegister af undef;
      setRegister cf (eq v_9016 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9016);
      pure ()
    pat_end
