def sarxl1 : instruction :=
  definst "sarxl" $ do
    pattern fun (v_3210 : reg (bv 32)) (v_3211 : reg (bv 32)) (v_3212 : reg (bv 32)) => do
      v_7090 <- getRegister v_3211;
      v_7091 <- getRegister v_3210;
      setRegister (lhs.of_reg v_3212) (ashr v_7090 (bv_and v_7091 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3200 : reg (bv 32)) (v_3199 : Mem) (v_3201 : reg (bv 32)) => do
      v_11416 <- evaluateAddress v_3199;
      v_11417 <- load v_11416 4;
      v_11418 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3201) (ashr v_11417 (bv_and v_11418 (expression.bv_nat 32 31)));
      pure ()
    pat_end
