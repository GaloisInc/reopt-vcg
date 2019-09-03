def incw1 : instruction :=
  definst "incw" $ do
    pattern fun (v_3011 : reg (bv 16)) => do
      v_5662 <- getRegister v_3011;
      v_5663 <- eval (add v_5662 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_3011) v_5663;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5662 0 1) (expression.bv_nat 1 1))) (eq (extract v_5662 1 16) (expression.bv_nat 15 32767))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5663 8 16));
      setRegister zf (zeroFlag v_5663);
      setRegister af (mux (eq (extract v_5662 12 16) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_5663 0 1);
      pure ()
    pat_end;
    pattern fun (v_3006 : Mem) => do
      v_10177 <- evaluateAddress v_3006;
      v_10178 <- load v_10177 2;
      v_10179 <- eval (add v_10178 (expression.bv_nat 16 1));
      store v_10177 v_10179 2;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_10178 0 1) (expression.bv_nat 1 1))) (eq (extract v_10178 1 16) (expression.bv_nat 15 32767))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10179 8 16));
      setRegister af (mux (eq (extract v_10178 12 16) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10179);
      setRegister sf (extract v_10179 0 1);
      pure ()
    pat_end
