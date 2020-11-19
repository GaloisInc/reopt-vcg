def setnge : instruction :=
  definst "setnge" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      store v_1 (mux (notBool_ (eq v_2 v_3)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister sf;
      v_2 <- getRegister of;
      setRegister (lhs.of_reg rh_0) (mux (notBool_ (eq v_1 v_2)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end
