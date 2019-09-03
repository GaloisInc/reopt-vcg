def tzcntw1 : instruction :=
  definst "tzcntw" $ do
    pattern fun (v_2506 : reg (bv 16)) (v_2507 : reg (bv 16)) => do
      v_4655 <- getRegister v_2506;
      v_4703 <- eval (mux (eq (extract v_4655 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_4655 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_4655 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_4655 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_4655 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_4655 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_4655 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_4655 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_4655 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_4655 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_4655 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_4655 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_4655 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_4655 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_4655 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_4655 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2507) v_4703;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_4703);
      setRegister sf undef;
      setRegister cf (mux (eq v_4703 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2499 : Mem) (v_2502 : reg (bv 16)) => do
      v_9148 <- evaluateAddress v_2499;
      v_9149 <- load v_9148 2;
      v_9197 <- eval (mux (eq (extract v_9149 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 16 0) (mux (eq (extract v_9149 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 16 1) (mux (eq (extract v_9149 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 16 2) (mux (eq (extract v_9149 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 16 3) (mux (eq (extract v_9149 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 16 4) (mux (eq (extract v_9149 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 16 5) (mux (eq (extract v_9149 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 16 6) (mux (eq (extract v_9149 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 16 7) (mux (eq (extract v_9149 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 16 8) (mux (eq (extract v_9149 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 16 9) (mux (eq (extract v_9149 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 16 10) (mux (eq (extract v_9149 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 16 11) (mux (eq (extract v_9149 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 16 12) (mux (eq (extract v_9149 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 16 13) (mux (eq (extract v_9149 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 16 14) (mux (eq (extract v_9149 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 15) (expression.bv_nat 16 16)))))))))))))))));
      setRegister (lhs.of_reg v_2502) v_9197;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9197);
      setRegister sf undef;
      setRegister cf (mux (eq v_9197 (expression.bv_nat 16 16)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
