def sarxq1 : instruction :=
  definst "sarxq" $ do
    pattern fun (v_3178 : reg (bv 64)) (v_3179 : reg (bv 64)) (v_3180 : reg (bv 64)) => do
      v_8151 <- getRegister v_3179;
      v_8154 <- getRegister v_3178;
      setRegister (lhs.of_reg v_3180) (ashr (mi 64 (svalueMInt v_8151)) (uvalueMInt (bv_and v_8154 (expression.bv_nat 64 63))));
      pure ()
    pat_end;
    pattern fun (v_3168 : reg (bv 64)) (v_3167 : Mem) (v_3169 : reg (bv 64)) => do
      v_13107 <- evaluateAddress v_3167;
      v_13108 <- load v_13107 8;
      v_13111 <- getRegister v_3168;
      setRegister (lhs.of_reg v_3169) (ashr (mi 64 (svalueMInt v_13108)) (uvalueMInt (bv_and v_13111 (expression.bv_nat 64 63))));
      pure ()
    pat_end
