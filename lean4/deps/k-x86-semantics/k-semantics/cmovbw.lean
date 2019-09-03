def cmovbw1 : instruction :=
  definst "cmovbw" $ do
    pattern fun (v_2497 : reg (bv 16)) (v_2498 : reg (bv 16)) => do
      v_4178 <- getRegister cf;
      v_4180 <- getRegister v_2497;
      v_4181 <- getRegister v_2498;
      setRegister (lhs.of_reg v_2498) (mux (eq v_4178 (expression.bv_nat 1 1)) v_4180 v_4181);
      pure ()
    pat_end;
    pattern fun (v_2494 : Mem) (v_2493 : reg (bv 16)) => do
      v_7907 <- getRegister cf;
      v_7909 <- evaluateAddress v_2494;
      v_7910 <- load v_7909 2;
      v_7911 <- getRegister v_2493;
      setRegister (lhs.of_reg v_2493) (mux (eq v_7907 (expression.bv_nat 1 1)) v_7910 v_7911);
      pure ()
    pat_end
