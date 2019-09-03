def lzcntw1 : instruction :=
  definst "lzcntw" $ do
    pattern fun (v_3042 : reg (bv 16)) (v_3043 : reg (bv 16)) => do
      v_5666 <- getRegister v_3042;
      v_5714 <- eval (mux (eq (extract v_5666 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_5666 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_5666 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_5666 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_5666 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_5666 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_5666 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_5666 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_5666 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_5666 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_5666 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_5666 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_5666 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_5666 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_5666 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_5666 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3043) v_5714;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_5714);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_5714 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3038 : Mem) (v_3039 : reg (bv 16)) => do
      v_9122 <- evaluateAddress v_3038;
      v_9123 <- load v_9122 2;
      v_9171 <- eval (mux (eq (extract v_9123 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_9123 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_9123 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_9123 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_9123 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_9123 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_9123 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_9123 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_9123 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_9123 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_9123 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_9123 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_9123 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_9123 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_9123 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_9123 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_3039) v_9171;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_9171);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_9171 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
