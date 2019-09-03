def sarx1 : instruction :=
  definst "sarx" $ do
    pattern fun (v_3140 : reg (bv 32)) (v_3141 : reg (bv 32)) (v_3142 : reg (bv 32)) => do
      v_10050 <- getRegister v_3141;
      v_10054 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3142) (ashr (mi (bitwidthMInt v_10050) (svalueMInt v_10050)) (uvalueMInt (bv_and v_10054 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3161 : reg (bv 64)) (v_3162 : reg (bv 64)) (v_3163 : reg (bv 64)) => do
      v_10070 <- getRegister v_3162;
      v_10074 <- getRegister v_3161;
      setRegister (lhs.of_reg v_3163) (ashr (mi (bitwidthMInt v_10070) (svalueMInt v_10070)) (uvalueMInt (bv_and v_10074 (expression.bv_nat 64 63))));
      pure ()
    pat_end;
    pattern fun (v_3131 : reg (bv 32)) (v_3130 : Mem) (v_3132 : reg (bv 32)) => do
      v_17723 <- evaluateAddress v_3130;
      v_17724 <- load v_17723 4;
      v_17728 <- getRegister v_3131;
      setRegister (lhs.of_reg v_3132) (ashr (mi (bitwidthMInt v_17724) (svalueMInt v_17724)) (uvalueMInt (bv_and v_17728 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3152 : reg (bv 64)) (v_3151 : Mem) (v_3153 : reg (bv 64)) => do
      v_17733 <- evaluateAddress v_3151;
      v_17734 <- load v_17733 8;
      v_17738 <- getRegister v_3152;
      setRegister (lhs.of_reg v_3153) (ashr (mi (bitwidthMInt v_17734) (svalueMInt v_17734)) (uvalueMInt (bv_and v_17738 (expression.bv_nat 64 63))));
      pure ()
    pat_end
