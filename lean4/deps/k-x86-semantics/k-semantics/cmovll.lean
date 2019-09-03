def cmovll1 : instruction :=
  definst "cmovll" $ do
    pattern fun (v_2701 : reg (bv 32)) (v_2702 : reg (bv 32)) => do
      v_4432 <- getRegister sf;
      v_4434 <- getRegister of;
      v_4438 <- getRegister v_2701;
      v_4439 <- getRegister v_2702;
      setRegister (lhs.of_reg v_2702) (mux (notBool_ (eq (eq v_4432 (expression.bv_nat 1 1)) (eq v_4434 (expression.bv_nat 1 1)))) v_4438 v_4439);
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2698 : reg (bv 32)) => do
      v_8049 <- getRegister sf;
      v_8051 <- getRegister of;
      v_8055 <- evaluateAddress v_2697;
      v_8056 <- load v_8055 4;
      v_8057 <- getRegister v_2698;
      setRegister (lhs.of_reg v_2698) (mux (notBool_ (eq (eq v_8049 (expression.bv_nat 1 1)) (eq v_8051 (expression.bv_nat 1 1)))) v_8056 v_8057);
      pure ()
    pat_end
