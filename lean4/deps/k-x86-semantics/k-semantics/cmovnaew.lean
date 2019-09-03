def cmovnaew1 : instruction :=
  definst "cmovnaew" $ do
    pattern fun (v_2734 : reg (bv 16)) (v_2735 : reg (bv 16)) => do
      v_4481 <- getRegister cf;
      v_4483 <- getRegister v_2734;
      v_4484 <- getRegister v_2735;
      setRegister (lhs.of_reg v_2735) (mux (eq v_4481 (expression.bv_nat 1 1)) v_4483 v_4484);
      pure ()
    pat_end;
    pattern fun (v_2731 : Mem) (v_2730 : reg (bv 16)) => do
      v_8123 <- getRegister cf;
      v_8125 <- evaluateAddress v_2731;
      v_8126 <- load v_8125 2;
      v_8127 <- getRegister v_2730;
      setRegister (lhs.of_reg v_2730) (mux (eq v_8123 (expression.bv_nat 1 1)) v_8126 v_8127);
      pure ()
    pat_end
