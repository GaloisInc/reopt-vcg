def cmovlw1 : instruction :=
  definst "cmovlw" $ do
    pattern fun (v_2707 : reg (bv 16)) (v_2708 : reg (bv 16)) => do
      v_4447 <- getRegister sf;
      v_4449 <- getRegister of;
      v_4453 <- getRegister v_2707;
      v_4454 <- getRegister v_2708;
      setRegister (lhs.of_reg v_2708) (mux (notBool_ (eq (eq v_4447 (expression.bv_nat 1 1)) (eq v_4449 (expression.bv_nat 1 1)))) v_4453 v_4454);
      pure ()
    pat_end;
    pattern fun (v_2704 : Mem) (v_2703 : reg (bv 16)) => do
      v_8098 <- getRegister sf;
      v_8100 <- getRegister of;
      v_8104 <- evaluateAddress v_2704;
      v_8105 <- load v_8104 2;
      v_8106 <- getRegister v_2703;
      setRegister (lhs.of_reg v_2703) (mux (notBool_ (eq (eq v_8098 (expression.bv_nat 1 1)) (eq v_8100 (expression.bv_nat 1 1)))) v_8105 v_8106);
      pure ()
    pat_end
