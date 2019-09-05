def cmovnbel1 : instruction :=
  definst "cmovnbel" $ do
    pattern fun (v_2836 : reg (bv 32)) (v_2837 : reg (bv 32)) => do
      v_4594 <- getRegister cf;
      v_4597 <- getRegister zf;
      v_4601 <- getRegister v_2836;
      v_4602 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2837) (mux (bit_and (notBool_ (eq v_4594 (expression.bv_nat 1 1))) (notBool_ (eq v_4597 (expression.bv_nat 1 1)))) v_4601 v_4602);
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2832 : reg (bv 32)) => do
      v_8146 <- getRegister cf;
      v_8149 <- getRegister zf;
      v_8153 <- evaluateAddress v_2829;
      v_8154 <- load v_8153 4;
      v_8155 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2832) (mux (bit_and (notBool_ (eq v_8146 (expression.bv_nat 1 1))) (notBool_ (eq v_8149 (expression.bv_nat 1 1)))) v_8154 v_8155);
      pure ()
    pat_end
