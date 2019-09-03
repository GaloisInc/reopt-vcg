def cmovgeq1 : instruction :=
  definst "cmovgeq" $ do
    pattern fun (v_2597 : reg (bv 64)) (v_2598 : reg (bv 64)) => do
      v_4284 <- getRegister sf;
      v_4286 <- getRegister of;
      v_4289 <- getRegister v_2597;
      v_4290 <- getRegister v_2598;
      setRegister (lhs.of_reg v_2598) (mux (eq (eq v_4284 (expression.bv_nat 1 1)) (eq v_4286 (expression.bv_nat 1 1))) v_4289 v_4290);
      pure ()
    pat_end;
    pattern fun (v_2589 : Mem) (v_2590 : reg (bv 64)) => do
      v_7941 <- getRegister sf;
      v_7943 <- getRegister of;
      v_7946 <- evaluateAddress v_2589;
      v_7947 <- load v_7946 8;
      v_7948 <- getRegister v_2590;
      setRegister (lhs.of_reg v_2590) (mux (eq (eq v_7941 (expression.bv_nat 1 1)) (eq v_7943 (expression.bv_nat 1 1))) v_7947 v_7948);
      pure ()
    pat_end
