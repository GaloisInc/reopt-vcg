def setle1 : instruction :=
  definst "setle" $ do
    pattern fun (v_2577 : reg (bv 8)) => do
      v_4045 <- getRegister zf;
      v_4046 <- getRegister sf;
      v_4047 <- getRegister of;
      setRegister (lhs.of_reg v_2577) (mux (bit_or v_4045 (notBool_ (eq v_4046 v_4047))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) => do
      v_7942 <- evaluateAddress v_2570;
      v_7943 <- getRegister zf;
      v_7944 <- getRegister sf;
      v_7945 <- getRegister of;
      store v_7942 (mux (bit_or v_7943 (notBool_ (eq v_7944 v_7945))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
