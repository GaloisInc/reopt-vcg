def incb1 : instruction :=
  definst "incb" $ do
    pattern fun (v_2984 : reg (bv 8)) => do
      v_5565 <- getRegister v_2984;
      v_5566 <- eval (add v_5565 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2984) v_5566;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5565 0 1) (expression.bv_nat 1 1))) (eq (extract v_5565 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5566 0 8));
      setRegister zf (zeroFlag v_5566);
      setRegister af (mux (eq (extract v_5565 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_5566 0 1);
      pure ()
    pat_end;
    pattern fun (v_2988 : reg (bv 8)) => do
      v_5587 <- getRegister v_2988;
      v_5588 <- eval (add v_5587 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2988) v_5588;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5587 0 1) (expression.bv_nat 1 1))) (eq (extract v_5587 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5588 0 8));
      setRegister af (mux (eq (extract v_5587 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5588);
      setRegister sf (extract v_5588 0 1);
      pure ()
    pat_end;
    pattern fun (v_2981 : Mem) => do
      v_10108 <- evaluateAddress v_2981;
      v_10109 <- load v_10108 1;
      v_10110 <- eval (add v_10109 (expression.bv_nat 8 1));
      store v_10108 v_10110 1;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_10109 0 1) (expression.bv_nat 1 1))) (eq (extract v_10109 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10110 0 8));
      setRegister af (mux (eq (extract v_10109 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10110);
      setRegister sf (extract v_10110 0 1);
      pure ()
    pat_end
