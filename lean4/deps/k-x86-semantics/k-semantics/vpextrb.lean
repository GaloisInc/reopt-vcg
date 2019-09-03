def vpextrb1 : instruction :=
  definst "vpextrb" $ do
    pattern fun (v_3107 : imm int) (v_3104 : reg (bv 128)) (v_3109 : reg (bv 32)) => do
      v_8724 <- getRegister v_3104;
      setRegister (lhs.of_reg v_3109) (concat (expression.bv_nat 24 0) (extract (lshr v_8724 (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3107 8 8) 4 8)) 3) 0 128))) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3113 : imm int) (v_3110 : reg (bv 128)) (v_3114 : reg (bv 64)) => do
      v_8735 <- getRegister v_3110;
      setRegister (lhs.of_reg v_3114) (concat (expression.bv_nat 56 0) (extract (lshr v_8735 (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3113 8 8) 4 8)) 3) 0 128))) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3103 : imm int) (v_3099 : reg (bv 128)) (v_3102 : Mem) => do
      v_19635 <- evaluateAddress v_3102;
      v_19636 <- getRegister v_3099;
      store v_19635 (extract (lshr v_19636 (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3103 8 8) 4 8)) 3) 0 128))) 120 128) 1;
      pure ()
    pat_end
