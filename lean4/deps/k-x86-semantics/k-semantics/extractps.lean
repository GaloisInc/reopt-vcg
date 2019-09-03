def extractps1 : instruction :=
  definst "extractps" $ do
    pattern fun (v_2809 : imm int) (v_2813 : reg (bv 128)) (v_2811 : reg (bv 32)) => do
      v_4952 <- getRegister v_2813;
      setRegister (lhs.of_reg v_2811) (extract (lshr v_4952 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2809 8 8) 6 8)) 5) 0 128))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2815 : imm int) (v_2819 : reg (bv 128)) (v_2817 : reg (bv 64)) => do
      v_4962 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2817) (concat (expression.bv_nat 32 0) (extract (lshr v_4962 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2815 8 8) 6 8)) 5) 0 128))) 96 128));
      pure ()
    pat_end;
    pattern fun (v_2804 : imm int) (v_2807 : reg (bv 128)) (v_2805 : Mem) => do
      v_10097 <- evaluateAddress v_2805;
      v_10098 <- getRegister v_2807;
      store v_10097 (extract (lshr v_10098 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2804 8 8) 6 8)) 5) 0 128))) 96 128) 4;
      pure ()
    pat_end
