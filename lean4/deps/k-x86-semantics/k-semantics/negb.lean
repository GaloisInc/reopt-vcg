def negb1 : instruction :=
  definst "negb" $ do
    pattern fun (v_2819 : reg (bv 8)) => do
      v_4334 <- getRegister v_2819;
      v_4341 <- eval (add (expression.bv_nat 8 1) (bv_xor v_4334 (mi (bitwidthMInt v_4334) -1)));
      v_4342 <- eval (extract v_4341 0 1);
      setRegister (lhs.of_reg v_2819) v_4341;
      setRegister of (mux (bit_and (eq (extract v_4334 0 1) (expression.bv_nat 1 1)) (eq v_4342 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4341 0 8));
      setRegister zf (zeroFlag v_4341);
      setRegister af (mux (notBool_ (eq (eq (extract v_4334 3 4) (expression.bv_nat 1 1)) (eq (extract v_4341 3 4) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4342;
      setRegister cf (mux (notBool_ (eq v_4334 (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2823 : reg (bv 8)) => do
      v_4365 <- getRegister v_2823;
      v_4372 <- eval (add (expression.bv_nat 8 1) (bv_xor v_4365 (mi (bitwidthMInt v_4365) -1)));
      v_4373 <- eval (extract v_4372 0 1);
      setRegister (lhs.of_reg v_2823) v_4372;
      setRegister of (mux (bit_and (eq (extract v_4365 0 1) (expression.bv_nat 1 1)) (eq v_4373 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4372 0 8));
      setRegister af (mux (notBool_ (eq (eq (extract v_4365 3 4) (expression.bv_nat 1 1)) (eq (extract v_4372 3 4) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4372);
      setRegister sf v_4373;
      setRegister cf (mux (notBool_ (eq v_4365 (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2815 : Mem) => do
      v_11010 <- evaluateAddress v_2815;
      v_11011 <- load v_11010 1;
      v_11015 <- eval (add (expression.bv_nat 8 1) (bv_xor v_11011 (mi (bitwidthMInt v_11011) -1)));
      store v_11010 v_11015 1;
      v_11020 <- eval (extract v_11015 0 1);
      setRegister of (mux (bit_and (eq (extract v_11011 0 1) (expression.bv_nat 1 1)) (eq v_11020 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11015 0 8));
      setRegister af (mux (notBool_ (eq (eq (extract v_11011 3 4) (expression.bv_nat 1 1)) (eq (extract v_11015 3 4) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_11015);
      setRegister sf v_11020;
      setRegister cf (mux (notBool_ (eq v_11011 (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
