def cmovnaeq1 : instruction :=
  definst "cmovnaeq" $ do
    pattern fun (v_2737 : reg (bv 64)) (v_2738 : reg (bv 64)) => do
      v_4484 <- getRegister cf;
      v_4486 <- getRegister v_2737;
      v_4487 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2738) (mux (eq v_4484 (expression.bv_nat 1 1)) v_4486 v_4487);
      pure ()
    pat_end;
    pattern fun (v_2733 : Mem) (v_2734 : reg (bv 64)) => do
      v_8089 <- getRegister cf;
      v_8091 <- evaluateAddress v_2733;
      v_8092 <- load v_8091 8;
      v_8093 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2734) (mux (eq v_8089 (expression.bv_nat 1 1)) v_8092 v_8093);
      pure ()
    pat_end
