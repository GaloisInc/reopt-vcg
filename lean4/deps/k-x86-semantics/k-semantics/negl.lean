def negl1 : instruction :=
  definst "negl" $ do
    pattern fun (v_2830 : reg (bv 32)) => do
      v_4399 <- getRegister v_2830;
      v_4406 <- eval (add (expression.bv_nat 32 1) (bv_xor v_4399 (mi (bitwidthMInt v_4399) -1)));
      v_4407 <- eval (extract v_4406 0 1);
      setRegister (lhs.of_reg v_2830) v_4406;
      setRegister of (mux (bit_and (eq (extract v_4399 0 1) (expression.bv_nat 1 1)) (eq v_4407 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4406 24 32));
      setRegister af (mux (notBool_ (eq (eq (extract v_4399 27 28) (expression.bv_nat 1 1)) (eq (extract v_4406 27 28) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4406);
      setRegister sf v_4407;
      setRegister cf (mux (notBool_ (eq v_4399 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2826 : Mem) => do
      v_11042 <- evaluateAddress v_2826;
      v_11043 <- load v_11042 4;
      v_11047 <- eval (add (expression.bv_nat 32 1) (bv_xor v_11043 (mi (bitwidthMInt v_11043) -1)));
      store v_11042 v_11047 4;
      v_11052 <- eval (extract v_11047 0 1);
      setRegister of (mux (bit_and (eq (extract v_11043 0 1) (expression.bv_nat 1 1)) (eq v_11052 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11047 24 32));
      setRegister af (mux (notBool_ (eq (eq (extract v_11043 27 28) (expression.bv_nat 1 1)) (eq (extract v_11047 27 28) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11047);
      setRegister sf v_11052;
      setRegister cf (mux (notBool_ (eq v_11043 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
