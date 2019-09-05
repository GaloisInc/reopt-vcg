def cmovnaeq1 : instruction :=
  definst "cmovnaeq" $ do
    pattern fun (v_2789 : reg (bv 64)) (v_2790 : reg (bv 64)) => do
      v_4535 <- getRegister cf;
      v_4537 <- getRegister v_2789;
      v_4538 <- getRegister v_2790;
      setRegister (lhs.of_reg v_2790) (mux (eq v_4535 (expression.bv_nat 1 1)) v_4537 v_4538);
      pure ()
    pat_end;
    pattern fun (v_2784 : Mem) (v_2785 : reg (bv 64)) => do
      v_8102 <- getRegister cf;
      v_8104 <- evaluateAddress v_2784;
      v_8105 <- load v_8104 8;
      v_8106 <- getRegister v_2785;
      setRegister (lhs.of_reg v_2785) (mux (eq v_8102 (expression.bv_nat 1 1)) v_8105 v_8106);
      pure ()
    pat_end
