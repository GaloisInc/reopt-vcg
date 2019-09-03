def incw1 : instruction :=
  definst "incw" $ do
    pattern fun (v_2998 : reg (bv 16)) => do
      v_5365 <- getRegister v_2998;
      v_5366 <- eval (add v_5365 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_2998) v_5366;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5365 0 1) (expression.bv_nat 1 1))) (eq (extract v_5365 1 16) (expression.bv_nat 15 32767))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5366 8 16));
      setRegister af (mux (eq (extract v_5365 12 16) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5366);
      setRegister sf (extract v_5366 0 1);
      pure ()
    pat_end;
    pattern fun (v_2995 : Mem) => do
      v_9588 <- evaluateAddress v_2995;
      v_9589 <- load v_9588 2;
      v_9590 <- eval (add v_9589 (expression.bv_nat 16 1));
      store v_9588 v_9590 2;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_9589 0 1) (expression.bv_nat 1 1))) (eq (extract v_9589 1 16) (expression.bv_nat 15 32767))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9590 8 16));
      setRegister af (mux (eq (extract v_9589 12 16) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9590);
      setRegister sf (extract v_9590 0 1);
      pure ()
    pat_end
