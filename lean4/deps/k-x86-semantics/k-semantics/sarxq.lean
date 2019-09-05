def sarxq1 : instruction :=
  definst "sarxq" $ do
    pattern fun (v_3231 : reg (bv 64)) (v_3232 : reg (bv 64)) (v_3233 : reg (bv 64)) => do
      v_7105 <- getRegister v_3232;
      v_7106 <- getRegister v_3231;
      setRegister (lhs.of_reg v_3233) (ashr v_7105 (bv_and v_7106 (expression.bv_nat 64 63)));
      pure ()
    pat_end;
    pattern fun (v_3221 : reg (bv 64)) (v_3220 : Mem) (v_3222 : reg (bv 64)) => do
      v_11423 <- evaluateAddress v_3220;
      v_11424 <- load v_11423 8;
      v_11425 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3222) (ashr v_11424 (bv_and v_11425 (expression.bv_nat 64 63)));
      pure ()
    pat_end
