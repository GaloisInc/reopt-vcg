def cmovngeq1 : instruction :=
  definst "cmovngeq" $ do
    pattern fun (v_2888 : reg (bv 64)) (v_2889 : reg (bv 64)) => do
      v_4688 <- getRegister sf;
      v_4690 <- getRegister of;
      v_4694 <- getRegister v_2888;
      v_4695 <- getRegister v_2889;
      setRegister (lhs.of_reg v_2889) (mux (notBool_ (eq (eq v_4688 (expression.bv_nat 1 1)) (eq v_4690 (expression.bv_nat 1 1)))) v_4694 v_4695);
      pure ()
    pat_end;
    pattern fun (v_2883 : Mem) (v_2884 : reg (bv 64)) => do
      v_8279 <- getRegister sf;
      v_8281 <- getRegister of;
      v_8285 <- evaluateAddress v_2883;
      v_8286 <- load v_8285 8;
      v_8287 <- getRegister v_2884;
      setRegister (lhs.of_reg v_2884) (mux (notBool_ (eq (eq v_8279 (expression.bv_nat 1 1)) (eq v_8281 (expression.bv_nat 1 1)))) v_8286 v_8287);
      pure ()
    pat_end
