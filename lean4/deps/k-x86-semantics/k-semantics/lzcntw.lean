def lzcntw1 : instruction :=
  definst "lzcntw" $ do
    pattern fun (v_3055 : reg (bv 16)) (v_3056 : reg (bv 16)) => do
      v_5963 <- getRegister v_3055;
      v_6011 <- eval (mux (eq (extract v_5963 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_5963 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_5963 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_5963 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_5963 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_5963 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_5963 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_5963 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_5963 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_5963 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_5963 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_5963 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_5963 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_5963 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_5963 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_5963 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3056) v_6011;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_6011);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_6011 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3051 : reg (bv 16)) => do
      v_9712 <- evaluateAddress v_3049;
      v_9713 <- load v_9712 2;
      v_9761 <- eval (mux (eq (extract v_9713 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_9713 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_9713 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_9713 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_9713 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_9713 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_9713 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_9713 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_9713 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_9713 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_9713 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_9713 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_9713 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_9713 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_9713 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_9713 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3051) v_9761;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_9761);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_9761 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
