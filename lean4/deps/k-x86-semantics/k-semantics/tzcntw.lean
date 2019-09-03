def tzcntw1 : instruction :=
  definst "tzcntw" $ do
    pattern fun (v_2519 : reg (bv 16)) (v_2520 : reg (bv 16)) => do
      v_4666 <- getRegister v_2519;
      v_4714 <- eval (mux (eq (extract v_4666 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_4666 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_4666 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_4666 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_4666 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_4666 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_4666 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_4666 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_4666 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_4666 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_4666 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_4666 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_4666 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_4666 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_4666 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_4666 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2520) v_4714;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_4714);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_4714 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2512 : Mem) (v_2515 : reg (bv 16)) => do
      v_10242 <- evaluateAddress v_2512;
      v_10243 <- load v_10242 2;
      v_10291 <- eval (mux (eq (extract v_10243 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_10243 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_10243 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_10243 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_10243 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_10243 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_10243 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_10243 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_10243 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_10243 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_10243 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_10243 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_10243 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_10243 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_10243 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_10243 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2515) v_10291;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_10291);
      setRegister sf undef;
      setRegister cf (mux (eq v_10291 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
