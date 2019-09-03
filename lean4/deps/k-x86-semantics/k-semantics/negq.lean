def negq1 : instruction :=
  definst "negq" $ do
    pattern fun (v_2837 : reg (bv 64)) => do
      v_4433 <- getRegister v_2837;
      v_4440 <- eval (add (expression.bv_nat 64 1) (bv_xor v_4433 (mi (bitwidthMInt v_4433) -1)));
      v_4441 <- eval (extract v_4440 0 1);
      setRegister (lhs.of_reg v_2837) v_4440;
      setRegister of (mux (bit_and (eq (extract v_4433 0 1) (expression.bv_nat 1 1)) (eq v_4441 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4440 56 64));
      setRegister af (mux (notBool_ (eq (eq (extract v_4433 59 60) (expression.bv_nat 1 1)) (eq (extract v_4440 59 60) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4440);
      setRegister sf v_4441;
      setRegister cf (mux (notBool_ (eq v_4433 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2833 : Mem) => do
      v_11074 <- evaluateAddress v_2833;
      v_11075 <- load v_11074 8;
      v_11079 <- eval (add (expression.bv_nat 64 1) (bv_xor v_11075 (mi (bitwidthMInt v_11075) -1)));
      store v_11074 v_11079 8;
      v_11084 <- eval (extract v_11079 0 1);
      setRegister of (mux (bit_and (eq (extract v_11075 0 1) (expression.bv_nat 1 1)) (eq v_11084 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11079 56 64));
      setRegister af (mux (notBool_ (eq (eq (extract v_11075 59 60) (expression.bv_nat 1 1)) (eq (extract v_11079 59 60) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11079);
      setRegister sf v_11084;
      setRegister cf (mux (notBool_ (eq v_11075 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
