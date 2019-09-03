def cmovnsq1 : instruction :=
  definst "cmovnsq" $ do
    pattern fun (v_3066 : reg (bv 64)) (v_3067 : reg (bv 64)) => do
      v_4944 <- getRegister sf;
      v_4947 <- getRegister v_3066;
      v_4948 <- getRegister v_3067;
      setRegister (lhs.of_reg v_3067) (mux (notBool_ (eq v_4944 (expression.bv_nat 1 1))) v_4947 v_4948);
      pure ()
    pat_end;
    pattern fun (v_3057 : Mem) (v_3058 : reg (bv 64)) => do
      v_8473 <- getRegister sf;
      v_8476 <- evaluateAddress v_3057;
      v_8477 <- load v_8476 8;
      v_8478 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3058) (mux (notBool_ (eq v_8473 (expression.bv_nat 1 1))) v_8477 v_8478);
      pure ()
    pat_end
