def setnb1 : instruction :=
  definst "setnb" $ do
    pattern fun (v_2515 : reg (bv 8)) => do
      v_4029 <- getRegister cf;
      setRegister (lhs.of_reg v_2515) (mux (notBool_ (eq v_4029 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2511 : Mem) => do
      v_9496 <- evaluateAddress v_2511;
      v_9497 <- getRegister cf;
      store v_9496 (mux (notBool_ (eq v_9497 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
