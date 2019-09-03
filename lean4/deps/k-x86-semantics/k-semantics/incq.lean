def incq1 : instruction :=
  definst "incq" $ do
    pattern fun (v_2991 : reg (bv 64)) => do
      v_5340 <- getRegister v_2991;
      v_5341 <- eval (add v_5340 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2991) v_5341;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5340 0 1) (expression.bv_nat 1 1))) (eq (extract v_5340 1 64) (expression.bv_nat 63 9223372036854775807))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5341 56 64));
      setRegister af (mux (eq (extract v_5340 60 64) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5341);
      setRegister sf (extract v_5341 0 1);
      pure ()
    pat_end;
    pattern fun (v_2988 : Mem) => do
      v_9565 <- evaluateAddress v_2988;
      v_9566 <- load v_9565 8;
      v_9567 <- eval (add v_9566 (expression.bv_nat 64 1));
      store v_9565 v_9567 8;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_9566 0 1) (expression.bv_nat 1 1))) (eq (extract v_9566 1 64) (expression.bv_nat 63 9223372036854775807))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9567 56 64));
      setRegister af (mux (eq (extract v_9566 60 64) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9567);
      setRegister sf (extract v_9567 0 1);
      pure ()
    pat_end
