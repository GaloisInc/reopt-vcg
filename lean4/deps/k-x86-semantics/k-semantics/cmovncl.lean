def cmovncl1 : instruction :=
  definst "cmovncl" $ do
    pattern fun (v_2836 : reg (bv 32)) (v_2837 : reg (bv 32)) => do
      v_4621 <- getRegister cf;
      v_4624 <- getRegister v_2836;
      v_4625 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2837) (mux (notBool_ (eq v_4621 (expression.bv_nat 1 1))) v_4624 v_4625);
      pure ()
    pat_end;
    pattern fun (v_2832 : Mem) (v_2833 : reg (bv 32)) => do
      v_8193 <- getRegister cf;
      v_8196 <- evaluateAddress v_2832;
      v_8197 <- load v_8196 4;
      v_8198 <- getRegister v_2833;
      setRegister (lhs.of_reg v_2833) (mux (notBool_ (eq v_8193 (expression.bv_nat 1 1))) v_8197 v_8198);
      pure ()
    pat_end
