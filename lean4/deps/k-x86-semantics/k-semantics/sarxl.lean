def sarxl1 : instruction :=
  definst "sarxl" $ do
    pattern fun (v_3145 : reg (bv 32)) (v_3146 : reg (bv 32)) (v_3147 : reg (bv 32)) => do
      v_8145 <- getRegister v_3146;
      v_8149 <- getRegister v_3145;
      setRegister (lhs.of_reg v_3147) (ashr (mi (bitwidthMInt v_8145) (svalueMInt v_8145)) (uvalueMInt (bv_and v_8149 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3136 : reg (bv 32)) (v_3133 : Mem) (v_3137 : reg (bv 32)) => do
      v_13173 <- evaluateAddress v_3133;
      v_13174 <- load v_13173 4;
      v_13178 <- getRegister v_3136;
      setRegister (lhs.of_reg v_3137) (ashr (mi (bitwidthMInt v_13174) (svalueMInt v_13174)) (uvalueMInt (bv_and v_13178 (expression.bv_nat 32 31))));
      pure ()
    pat_end
