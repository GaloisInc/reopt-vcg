def negw1 : instruction :=
  definst "negw" $ do
    pattern fun (v_2844 : reg (bv 16)) => do
      v_4467 <- getRegister v_2844;
      v_4474 <- eval (add (expression.bv_nat 16 1) (bv_xor v_4467 (mi (bitwidthMInt v_4467) -1)));
      v_4475 <- eval (extract v_4474 0 1);
      setRegister (lhs.of_reg v_2844) v_4474;
      setRegister of (mux (bit_and (eq (extract v_4467 0 1) (expression.bv_nat 1 1)) (eq v_4475 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4474 8 16));
      setRegister af (mux (notBool_ (eq (eq (extract v_4467 11 12) (expression.bv_nat 1 1)) (eq (extract v_4474 11 12) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4474);
      setRegister sf v_4475;
      setRegister cf (mux (notBool_ (eq v_4467 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) => do
      v_11106 <- evaluateAddress v_2840;
      v_11107 <- load v_11106 2;
      v_11111 <- eval (add (expression.bv_nat 16 1) (bv_xor v_11107 (mi (bitwidthMInt v_11107) -1)));
      store v_11106 v_11111 2;
      v_11116 <- eval (extract v_11111 0 1);
      setRegister of (mux (bit_and (eq (extract v_11107 0 1) (expression.bv_nat 1 1)) (eq v_11116 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11111 8 16));
      setRegister af (mux (notBool_ (eq (eq (extract v_11107 11 12) (expression.bv_nat 1 1)) (eq (extract v_11111 11 12) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11111);
      setRegister sf v_11116;
      setRegister cf (mux (notBool_ (eq v_11107 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
