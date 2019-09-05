def cmovlq1 : instruction :=
  definst "cmovlq" $ do
    pattern fun (v_2762 : reg (bv 64)) (v_2763 : reg (bv 64)) => do
      v_4497 <- getRegister sf;
      v_4499 <- getRegister of;
      v_4503 <- getRegister v_2762;
      v_4504 <- getRegister v_2763;
      setRegister (lhs.of_reg v_2763) (mux (notBool_ (eq (eq v_4497 (expression.bv_nat 1 1)) (eq v_4499 (expression.bv_nat 1 1)))) v_4503 v_4504);
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) (v_2758 : reg (bv 64)) => do
      v_8073 <- getRegister sf;
      v_8075 <- getRegister of;
      v_8079 <- evaluateAddress v_2757;
      v_8080 <- load v_8079 8;
      v_8081 <- getRegister v_2758;
      setRegister (lhs.of_reg v_2758) (mux (notBool_ (eq (eq v_8073 (expression.bv_nat 1 1)) (eq v_8075 (expression.bv_nat 1 1)))) v_8080 v_8081);
      pure ()
    pat_end
