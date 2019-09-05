def setnp1 : instruction :=
  definst "setnp" $ do
    pattern fun (v_2682 : reg (bv 8)) => do
      v_4257 <- getRegister pf;
      setRegister (lhs.of_reg v_2682) (mux (notBool_ (eq v_4257 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2674 : Mem) => do
      v_8618 <- evaluateAddress v_2674;
      v_8619 <- getRegister pf;
      store v_8618 (mux (notBool_ (eq v_8619 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
