def cmovnbel1 : instruction :=
  definst "cmovnbel" $ do
    pattern fun (v_2770 : reg (bv 32)) (v_2771 : reg (bv 32)) => do
      v_4530 <- getRegister cf;
      v_4533 <- getRegister zf;
      v_4537 <- getRegister v_2770;
      v_4538 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2771) (mux (bit_and (notBool_ (eq v_4530 (expression.bv_nat 1 1))) (notBool_ (eq v_4533 (expression.bv_nat 1 1)))) v_4537 v_4538);
      pure ()
    pat_end;
    pattern fun (v_2766 : Mem) (v_2767 : reg (bv 32)) => do
      v_8160 <- getRegister cf;
      v_8163 <- getRegister zf;
      v_8167 <- evaluateAddress v_2766;
      v_8168 <- load v_8167 4;
      v_8169 <- getRegister v_2767;
      setRegister (lhs.of_reg v_2767) (mux (bit_and (notBool_ (eq v_8160 (expression.bv_nat 1 1))) (notBool_ (eq v_8163 (expression.bv_nat 1 1)))) v_8168 v_8169);
      pure ()
    pat_end
