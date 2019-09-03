def incl1 : instruction :=
  definst "incl" $ do
    pattern fun (v_2996 : reg (bv 32)) => do
      v_5612 <- getRegister v_2996;
      v_5613 <- eval (add v_5612 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2996) v_5613;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5612 0 1) (expression.bv_nat 1 1))) (eq (extract v_5612 1 32) (expression.bv_nat 31 2147483647))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5613 24 32));
      setRegister af (mux (eq (extract v_5612 28 32) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5613);
      setRegister sf (extract v_5613 0 1);
      pure ()
    pat_end;
    pattern fun (v_2992 : Mem) => do
      v_10131 <- evaluateAddress v_2992;
      v_10132 <- load v_10131 4;
      v_10133 <- eval (add v_10132 (expression.bv_nat 32 1));
      store v_10131 v_10133 4;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_10132 0 1) (expression.bv_nat 1 1))) (eq (extract v_10132 1 32) (expression.bv_nat 31 2147483647))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10133 24 32));
      setRegister af (mux (eq (extract v_10132 28 32) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10133);
      setRegister sf (extract v_10133 0 1);
      pure ()
    pat_end
