def sarx1 : instruction :=
  definst "sarx" $ do
    pattern fun (v_3151 : reg (bv 32)) (v_3152 : reg (bv 32)) (v_3153 : reg (bv 32)) => do
      v_9948 <- getRegister v_3152;
      v_9951 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3153) (ashr (mi 32 (svalueMInt v_9948)) (uvalueMInt (bv_and v_9951 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3172 : reg (bv 64)) (v_3173 : reg (bv 64)) (v_3174 : reg (bv 64)) => do
      v_9967 <- getRegister v_3173;
      v_9970 <- getRegister v_3172;
      setRegister (lhs.of_reg v_3174) (ashr (mi 64 (svalueMInt v_9967)) (uvalueMInt (bv_and v_9970 (expression.bv_nat 64 63))));
      pure ()
    pat_end;
    pattern fun (v_3142 : reg (bv 32)) (v_3141 : Mem) (v_3143 : reg (bv 32)) => do
      v_17491 <- evaluateAddress v_3141;
      v_17492 <- load v_17491 4;
      v_17495 <- getRegister v_3142;
      setRegister (lhs.of_reg v_3143) (ashr (mi 32 (svalueMInt v_17492)) (uvalueMInt (bv_and v_17495 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3162 : reg (bv 64)) (v_3164 : Mem) (v_3163 : reg (bv 64)) => do
      v_17500 <- evaluateAddress v_3164;
      v_17501 <- load v_17500 8;
      v_17504 <- getRegister v_3162;
      setRegister (lhs.of_reg v_3163) (ashr (mi 64 (svalueMInt v_17501)) (uvalueMInt (bv_and v_17504 (expression.bv_nat 64 63))));
      pure ()
    pat_end
