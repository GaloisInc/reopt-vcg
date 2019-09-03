def negb1 : instruction :=
  definst "negb" $ do
    pattern fun (v_2831 : reg (bv 8)) => do
      v_4443 <- getRegister v_2831;
      v_4448 <- eval (add (expression.bv_nat 8 1) (bv_xor v_4443 (expression.bv_nat 8 255)));
      v_4449 <- eval (extract v_4448 0 1);
      setRegister (lhs.of_reg v_2831) v_4448;
      setRegister of (mux (bit_and (eq (extract v_4443 0 1) (expression.bv_nat 1 1)) (eq v_4449 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4448 0 8));
      setRegister af (mux (notBool_ (eq (eq (extract v_4443 3 4) (expression.bv_nat 1 1)) (eq (extract v_4448 3 4) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4448);
      setRegister sf v_4449;
      setRegister cf (mux (notBool_ (eq v_4443 (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2828 : Mem) => do
      v_10978 <- evaluateAddress v_2828;
      v_10979 <- load v_10978 1;
      v_10981 <- eval (add (expression.bv_nat 8 1) (bv_xor v_10979 (expression.bv_nat 8 255)));
      store v_10978 v_10981 1;
      v_10986 <- eval (extract v_10981 0 1);
      setRegister of (mux (bit_and (eq (extract v_10979 0 1) (expression.bv_nat 1 1)) (eq v_10986 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10981 0 8));
      setRegister af (mux (notBool_ (eq (eq (extract v_10979 3 4) (expression.bv_nat 1 1)) (eq (extract v_10981 3 4) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10981);
      setRegister sf v_10986;
      setRegister cf (mux (notBool_ (eq v_10979 (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
