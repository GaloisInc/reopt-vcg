def sarxq1 : instruction :=
  definst "sarxq" $ do
    pattern fun (v_3167 : reg (bv 64)) (v_3168 : reg (bv 64)) (v_3169 : reg (bv 64)) => do
      v_8164 <- getRegister v_3168;
      v_8168 <- getRegister v_3167;
      setRegister (lhs.of_reg v_3169) (ashr (mi (bitwidthMInt v_8164) (svalueMInt v_8164)) (uvalueMInt (bv_and v_8168 (expression.bv_nat 64 63))));
      pure ()
    pat_end;
    pattern fun (v_3157 : reg (bv 64)) (v_3154 : Mem) (v_3158 : reg (bv 64)) => do
      v_13184 <- evaluateAddress v_3154;
      v_13185 <- load v_13184 8;
      v_13189 <- getRegister v_3157;
      setRegister (lhs.of_reg v_3158) (ashr (mi (bitwidthMInt v_13185) (svalueMInt v_13185)) (uvalueMInt (bv_and v_13189 (expression.bv_nat 64 63))));
      pure ()
    pat_end
