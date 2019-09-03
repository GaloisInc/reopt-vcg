def setp1 : instruction :=
  definst "setp" $ do
    pattern fun (v_2671 : reg (bv 8)) => do
      v_4251 <- getRegister pf;
      setRegister (lhs.of_reg v_2671) (mux (eq v_4251 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) => do
      v_9618 <- evaluateAddress v_2667;
      v_9619 <- getRegister pf;
      store v_9618 (mux (eq v_9619 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
