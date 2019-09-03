def cmovnbel1 : instruction :=
  definst "cmovnbel" $ do
    pattern fun (v_2782 : reg (bv 32)) (v_2783 : reg (bv 32)) => do
      v_4543 <- getRegister cf;
      v_4546 <- getRegister zf;
      v_4550 <- getRegister v_2782;
      v_4551 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2783) (mux (bit_and (notBool_ (eq v_4543 (expression.bv_nat 1 1))) (notBool_ (eq v_4546 (expression.bv_nat 1 1)))) v_4550 v_4551);
      pure ()
    pat_end;
    pattern fun (v_2778 : Mem) (v_2779 : reg (bv 32)) => do
      v_8133 <- getRegister cf;
      v_8136 <- getRegister zf;
      v_8140 <- evaluateAddress v_2778;
      v_8141 <- load v_8140 4;
      v_8142 <- getRegister v_2779;
      setRegister (lhs.of_reg v_2779) (mux (bit_and (notBool_ (eq v_8133 (expression.bv_nat 1 1))) (notBool_ (eq v_8136 (expression.bv_nat 1 1)))) v_8141 v_8142);
      pure ()
    pat_end
