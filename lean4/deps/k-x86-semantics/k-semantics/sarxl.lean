def sarxl1 : instruction :=
  definst "sarxl" $ do
    pattern fun (v_3157 : reg (bv 32)) (v_3158 : reg (bv 32)) (v_3159 : reg (bv 32)) => do
      v_8133 <- getRegister v_3158;
      v_8136 <- getRegister v_3157;
      setRegister (lhs.of_reg v_3159) (ashr (mi 32 (svalueMInt v_8133)) (uvalueMInt (bv_and v_8136 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3147 : reg (bv 32)) (v_3146 : Mem) (v_3148 : reg (bv 32)) => do
      v_13097 <- evaluateAddress v_3146;
      v_13098 <- load v_13097 4;
      v_13101 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3148) (ashr (mi 32 (svalueMInt v_13098)) (uvalueMInt (bv_and v_13101 (expression.bv_nat 32 31))));
      pure ()
    pat_end
