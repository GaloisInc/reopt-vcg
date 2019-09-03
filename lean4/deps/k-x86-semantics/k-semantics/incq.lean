def incq1 : instruction :=
  definst "incq" $ do
    pattern fun (v_3003 : reg (bv 64)) => do
      v_5637 <- getRegister v_3003;
      v_5638 <- eval (add v_5637 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_3003) v_5638;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5637 0 1) (expression.bv_nat 1 1))) (eq (extract v_5637 1 64) (expression.bv_nat 63 9223372036854775807))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5638 56 64));
      setRegister af (mux (eq (extract v_5637 60 64) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5638);
      setRegister sf (extract v_5638 0 1);
      pure ()
    pat_end;
    pattern fun (v_2999 : Mem) => do
      v_10154 <- evaluateAddress v_2999;
      v_10155 <- load v_10154 8;
      v_10156 <- eval (add v_10155 (expression.bv_nat 64 1));
      store v_10154 v_10156 8;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_10155 0 1) (expression.bv_nat 1 1))) (eq (extract v_10155 1 64) (expression.bv_nat 63 9223372036854775807))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10156 56 64));
      setRegister af (mux (eq (extract v_10155 60 64) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10156);
      setRegister sf (extract v_10156 0 1);
      pure ()
    pat_end
