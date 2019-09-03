def incb1 : instruction :=
  definst "incb" $ do
    pattern fun (v_2973 : reg (bv 8)) => do
      v_5268 <- getRegister v_2973;
      v_5269 <- eval (add v_5268 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2973) v_5269;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5268 0 1) (expression.bv_nat 1 1))) (eq (extract v_5268 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5269 0 8));
      setRegister af (mux (eq (extract v_5268 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5269);
      setRegister sf (extract v_5269 0 1);
      pure ()
    pat_end;
    pattern fun (v_2977 : reg (bv 8)) => do
      v_5290 <- getRegister v_2977;
      v_5291 <- eval (add v_5290 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2977) v_5291;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5290 0 1) (expression.bv_nat 1 1))) (eq (extract v_5290 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5291 0 8));
      setRegister zf (zeroFlag v_5291);
      setRegister af (mux (eq (extract v_5290 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_5291 0 1);
      pure ()
    pat_end;
    pattern fun (v_2970 : Mem) => do
      v_9519 <- evaluateAddress v_2970;
      v_9520 <- load v_9519 1;
      v_9521 <- eval (add v_9520 (expression.bv_nat 8 1));
      store v_9519 v_9521 1;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_9520 0 1) (expression.bv_nat 1 1))) (eq (extract v_9520 1 8) (expression.bv_nat 7 127))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9521 0 8));
      setRegister af (mux (eq (extract v_9520 4 8) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9521);
      setRegister sf (extract v_9521 0 1);
      pure ()
    pat_end
