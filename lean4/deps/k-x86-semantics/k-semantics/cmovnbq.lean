def cmovnbq1 : instruction :=
  definst "cmovnbq" $ do
    pattern fun (v_2807 : reg (bv 64)) (v_2808 : reg (bv 64)) => do
      v_4586 <- getRegister cf;
      v_4589 <- getRegister v_2807;
      v_4590 <- getRegister v_2808;
      setRegister (lhs.of_reg v_2808) (mux (notBool_ (eq v_4586 (expression.bv_nat 1 1))) v_4589 v_4590);
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2803 : reg (bv 64)) => do
      v_8204 <- getRegister cf;
      v_8207 <- evaluateAddress v_2802;
      v_8208 <- load v_8207 8;
      v_8209 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2803) (mux (notBool_ (eq v_8204 (expression.bv_nat 1 1))) v_8208 v_8209);
      pure ()
    pat_end
