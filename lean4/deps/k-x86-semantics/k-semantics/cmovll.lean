def cmovll1 : instruction :=
  definst "cmovll" $ do
    pattern fun (v_2689 : reg (bv 32)) (v_2690 : reg (bv 32)) => do
      v_4419 <- getRegister sf;
      v_4421 <- getRegister of;
      v_4425 <- getRegister v_2689;
      v_4426 <- getRegister v_2690;
      setRegister (lhs.of_reg v_2690) (mux (notBool_ (eq (eq v_4419 (expression.bv_nat 1 1)) (eq v_4421 (expression.bv_nat 1 1)))) v_4425 v_4426);
      pure ()
    pat_end;
    pattern fun (v_2685 : Mem) (v_2686 : reg (bv 32)) => do
      v_8076 <- getRegister sf;
      v_8078 <- getRegister of;
      v_8082 <- evaluateAddress v_2685;
      v_8083 <- load v_8082 4;
      v_8084 <- getRegister v_2686;
      setRegister (lhs.of_reg v_2686) (mux (notBool_ (eq (eq v_8076 (expression.bv_nat 1 1)) (eq v_8078 (expression.bv_nat 1 1)))) v_8083 v_8084);
      pure ()
    pat_end
