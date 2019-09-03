def decw1 : instruction :=
  definst "decw" $ do
    pattern fun (v_2712 : reg (bv 16)) => do
      v_4472 <- getRegister v_2712;
      v_4473 <- eval (sub v_4472 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_2712) v_4473;
      setRegister of (mux (bit_and (eq (extract v_4472 0 1) (expression.bv_nat 1 1)) (eq (extract v_4472 1 16) (expression.bv_nat 15 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4473 8 16));
      setRegister zf (zeroFlag v_4473);
      setRegister af (mux (eq (extract v_4472 12 16) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_4473 0 1);
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) => do
      v_10075 <- evaluateAddress v_2707;
      v_10076 <- load v_10075 2;
      v_10077 <- eval (sub v_10076 (expression.bv_nat 16 1));
      store v_10075 v_10077 2;
      setRegister of (mux (bit_and (eq (extract v_10076 0 1) (expression.bv_nat 1 1)) (eq (extract v_10076 1 16) (expression.bv_nat 15 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10077 8 16));
      setRegister af (mux (eq (extract v_10076 12 16) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10077);
      setRegister sf (extract v_10077 0 1);
      pure ()
    pat_end
