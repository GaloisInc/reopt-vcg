def decl1 : instruction :=
  definst "decl" $ do
    pattern fun (v_2697 : reg (bv 32)) => do
      v_4424 <- getRegister v_2697;
      v_4425 <- eval (sub v_4424 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2697) v_4425;
      setRegister of (mux (bit_and (eq (extract v_4424 0 1) (expression.bv_nat 1 1)) (eq (extract v_4424 1 32) (expression.bv_nat 31 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4425 24 32));
      setRegister af (mux (eq (extract v_4424 28 32) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4425);
      setRegister sf (extract v_4425 0 1);
      pure ()
    pat_end;
    pattern fun (v_2693 : Mem) => do
      v_10031 <- evaluateAddress v_2693;
      v_10032 <- load v_10031 4;
      v_10033 <- eval (sub v_10032 (expression.bv_nat 32 1));
      store v_10031 v_10033 4;
      setRegister of (mux (bit_and (eq (extract v_10032 0 1) (expression.bv_nat 1 1)) (eq (extract v_10032 1 32) (expression.bv_nat 31 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10033 24 32));
      setRegister af (mux (eq (extract v_10032 28 32) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10033);
      setRegister sf (extract v_10033 0 1);
      pure ()
    pat_end
