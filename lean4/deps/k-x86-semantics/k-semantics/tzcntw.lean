def tzcntw1 : instruction :=
  definst "tzcntw" $ do
    pattern fun (v_2595 : reg (bv 16)) (v_2596 : reg (bv 16)) => do
      v_4677 <- getRegister v_2595;
      v_4709 <- eval (mux (isBitSet v_4677 15) (expression.bv_nat 16 0) (mux (isBitSet v_4677 14) (expression.bv_nat 16 1) (mux (isBitSet v_4677 13) (expression.bv_nat 16 2) (mux (isBitSet v_4677 12) (expression.bv_nat 16 3) (mux (isBitSet v_4677 11) (expression.bv_nat 16 4) (mux (isBitSet v_4677 10) (expression.bv_nat 16 5) (mux (isBitSet v_4677 9) (expression.bv_nat 16 6) (mux (isBitSet v_4677 8) (expression.bv_nat 16 7) (mux (isBitSet v_4677 7) (expression.bv_nat 16 8) (mux (isBitSet v_4677 6) (expression.bv_nat 16 9) (mux (isBitSet v_4677 5) (expression.bv_nat 16 10) (mux (isBitSet v_4677 4) (expression.bv_nat 16 11) (mux (isBitSet v_4677 3) (expression.bv_nat 16 12) (mux (isBitSet v_4677 2) (expression.bv_nat 16 13) (mux (isBitSet v_4677 1) (expression.bv_nat 16 14) (mux (isBitSet v_4677 0) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2596) v_4709;
      setRegister af undef;
      setRegister cf (eq v_4709 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_4709);
      pure ()
    pat_end;
    pattern fun (v_2590 : Mem) (v_2591 : reg (bv 16)) => do
      v_9010 <- evaluateAddress v_2590;
      v_9011 <- load v_9010 2;
      v_9043 <- eval (mux (isBitSet v_9011 15) (expression.bv_nat 16 0) (mux (isBitSet v_9011 14) (expression.bv_nat 16 1) (mux (isBitSet v_9011 13) (expression.bv_nat 16 2) (mux (isBitSet v_9011 12) (expression.bv_nat 16 3) (mux (isBitSet v_9011 11) (expression.bv_nat 16 4) (mux (isBitSet v_9011 10) (expression.bv_nat 16 5) (mux (isBitSet v_9011 9) (expression.bv_nat 16 6) (mux (isBitSet v_9011 8) (expression.bv_nat 16 7) (mux (isBitSet v_9011 7) (expression.bv_nat 16 8) (mux (isBitSet v_9011 6) (expression.bv_nat 16 9) (mux (isBitSet v_9011 5) (expression.bv_nat 16 10) (mux (isBitSet v_9011 4) (expression.bv_nat 16 11) (mux (isBitSet v_9011 3) (expression.bv_nat 16 12) (mux (isBitSet v_9011 2) (expression.bv_nat 16 13) (mux (isBitSet v_9011 1) (expression.bv_nat 16 14) (mux (isBitSet v_9011 0) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2591) v_9043;
      setRegister af undef;
      setRegister cf (eq v_9043 (expression.bv_nat 16 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9043);
      pure ()
    pat_end
