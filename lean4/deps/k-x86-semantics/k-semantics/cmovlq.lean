def cmovlq1 : instruction :=
  definst "cmovlq" $ do
    pattern fun (v_2710 : reg (bv 64)) (v_2711 : reg (bv 64)) => do
      v_4446 <- getRegister sf;
      v_4448 <- getRegister of;
      v_4452 <- getRegister v_2710;
      v_4453 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2711) (mux (notBool_ (eq (eq v_4446 (expression.bv_nat 1 1)) (eq v_4448 (expression.bv_nat 1 1)))) v_4452 v_4453);
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 64)) => do
      v_8060 <- getRegister sf;
      v_8062 <- getRegister of;
      v_8066 <- evaluateAddress v_2706;
      v_8067 <- load v_8066 8;
      v_8068 <- getRegister v_2707;
      setRegister (lhs.of_reg v_2707) (mux (notBool_ (eq (eq v_8060 (expression.bv_nat 1 1)) (eq v_8062 (expression.bv_nat 1 1)))) v_8067 v_8068);
      pure ()
    pat_end
