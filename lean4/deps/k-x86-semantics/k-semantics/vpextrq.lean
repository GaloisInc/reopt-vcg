def vpextrq1 : instruction :=
  definst "vpextrq" $ do
    pattern fun (v_3119 : imm int) (v_3123 : reg (bv 128)) (v_3124 : reg (bv 64)) => do
      v_8914 <- getRegister v_3123;
      v_8917 <- eval (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3119 8 8) 7 8));
      setRegister (lhs.of_reg v_3124) (extract (lshr v_8914 (uvalueMInt (extract (shl v_8917 6) 0 (bitwidthMInt v_8917)))) 64 128);
      pure ()
    pat_end;
    pattern fun (v_3114 : imm int) (v_3118 : reg (bv 128)) (v_3117 : Mem) => do
      v_20384 <- evaluateAddress v_3117;
      v_20385 <- getRegister v_3118;
      v_20388 <- eval (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3114 8 8) 7 8));
      store v_20384 (extract (lshr v_20385 (uvalueMInt (extract (shl v_20388 6) 0 (bitwidthMInt v_20388)))) 64 128) 8;
      pure ()
    pat_end
