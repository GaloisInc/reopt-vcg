def vpextrd1 : instruction :=
  definst "vpextrd" $ do
    pattern fun (v_3108 : imm int) (v_3112 : reg (bv 128)) (v_3113 : reg (bv 32)) => do
      v_8898 <- getRegister v_3112;
      v_8901 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3108 8 8) 6 8));
      setRegister (lhs.of_reg v_3113) (extract (lshr v_8898 (uvalueMInt (extract (shl v_8901 5) 0 (bitwidthMInt v_8901)))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_3103 : imm int) (v_3107 : reg (bv 128)) (v_3106 : Mem) => do
      v_20372 <- evaluateAddress v_3106;
      v_20373 <- getRegister v_3107;
      v_20376 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3103 8 8) 6 8));
      store v_20372 (extract (lshr v_20373 (uvalueMInt (extract (shl v_20376 5) 0 (bitwidthMInt v_20376)))) 96 128) 4;
      pure ()
    pat_end
