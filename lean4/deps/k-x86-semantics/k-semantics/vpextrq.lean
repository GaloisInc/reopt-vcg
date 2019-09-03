def vpextrq1 : instruction :=
  definst "vpextrq" $ do
    pattern fun (v_3135 : imm int) (v_3132 : reg (bv 128)) (v_3136 : reg (bv 64)) => do
      v_8766 <- getRegister v_3132;
      setRegister (lhs.of_reg v_3136) (extract (lshr v_8766 (uvalueMInt (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3135 8 8) 7 8)) 6) 0 128))) 64 128);
      pure ()
    pat_end;
    pattern fun (v_3131 : imm int) (v_3127 : reg (bv 128)) (v_3130 : Mem) => do
      v_19657 <- evaluateAddress v_3130;
      v_19658 <- getRegister v_3127;
      store v_19657 (extract (lshr v_19658 (uvalueMInt (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3131 8 8) 7 8)) 6) 0 128))) 64 128) 8;
      pure ()
    pat_end
