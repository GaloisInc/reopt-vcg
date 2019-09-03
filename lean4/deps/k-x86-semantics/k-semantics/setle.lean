def setle1 : instruction :=
  definst "setle" $ do
    pattern fun (v_2495 : reg (bv 8)) => do
      v_3989 <- getRegister zf;
      v_3991 <- getRegister sf;
      v_3993 <- getRegister of;
      setRegister (lhs.of_reg v_2495) (mux (bit_or (eq v_3989 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_3991 (expression.bv_nat 1 1)) (eq v_3993 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2491 : Mem) => do
      v_9495 <- evaluateAddress v_2491;
      v_9496 <- getRegister zf;
      v_9498 <- getRegister sf;
      v_9500 <- getRegister of;
      store v_9495 (mux (bit_or (eq v_9496 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9498 (expression.bv_nat 1 1)) (eq v_9500 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
