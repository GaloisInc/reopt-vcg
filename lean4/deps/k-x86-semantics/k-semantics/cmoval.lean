def cmoval1 : instruction :=
  definst "cmoval" $ do
    pattern fun (v_2467 : reg (bv 32)) (v_2468 : reg (bv 32)) => do
      v_4123 <- getRegister cf;
      v_4126 <- getRegister zf;
      v_4130 <- getRegister v_2467;
      v_4131 <- getRegister v_2468;
      setRegister (lhs.of_reg v_2468) (mux (bit_and (notBool_ (eq v_4123 (expression.bv_nat 1 1))) (notBool_ (eq v_4126 (expression.bv_nat 1 1)))) v_4130 v_4131);
      pure ()
    pat_end;
    pattern fun (v_2460 : Mem) (v_2463 : reg (bv 32)) => do
      v_7810 <- getRegister cf;
      v_7813 <- getRegister zf;
      v_7817 <- evaluateAddress v_2460;
      v_7818 <- load v_7817 4;
      v_7819 <- getRegister v_2463;
      setRegister (lhs.of_reg v_2463) (mux (bit_and (notBool_ (eq v_7810 (expression.bv_nat 1 1))) (notBool_ (eq v_7813 (expression.bv_nat 1 1)))) v_7818 v_7819);
      pure ()
    pat_end
