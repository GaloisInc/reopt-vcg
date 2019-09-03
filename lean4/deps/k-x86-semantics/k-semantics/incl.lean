def incl1 : instruction :=
  definst "incl" $ do
    pattern fun (v_2984 : reg (bv 32)) => do
      v_5315 <- getRegister v_2984;
      v_5316 <- eval (add v_5315 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2984) v_5316;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_5315 0 1) (expression.bv_nat 1 1))) (eq (extract v_5315 1 32) (expression.bv_nat 31 2147483647))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5316 24 32));
      setRegister zf (zeroFlag v_5316);
      setRegister af (mux (eq (extract v_5315 28 32) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_5316 0 1);
      pure ()
    pat_end;
    pattern fun (v_2981 : Mem) => do
      v_9542 <- evaluateAddress v_2981;
      v_9543 <- load v_9542 4;
      v_9544 <- eval (add v_9543 (expression.bv_nat 32 1));
      store v_9542 v_9544 4;
      setRegister of (mux (bit_and (notBool_ (eq (extract v_9543 0 1) (expression.bv_nat 1 1))) (eq (extract v_9543 1 32) (expression.bv_nat 31 2147483647))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9544 24 32));
      setRegister af (mux (eq (extract v_9543 28 32) (expression.bv_nat 4 15)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9544);
      setRegister sf (extract v_9544 0 1);
      pure ()
    pat_end
