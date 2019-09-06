def sets1 : instruction :=
  definst "sets" $ do
    pattern fun (v_2786 : reg (bv 8)) => do
      v_4279 <- getRegister sf;
      setRegister (lhs.of_reg v_2786) (mux v_4279 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2779 : Mem) => do
      v_8052 <- evaluateAddress v_2779;
      v_8053 <- getRegister sf;
      store v_8052 (mux v_8053 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
