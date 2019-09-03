def rorx1 : instruction :=
  definst "rorx" $ do
    pattern fun (v_2783 : imm int) (v_2784 : reg (bv 32)) (v_2785 : reg (bv 32)) => do
      v_9214 <- getRegister v_2784;
      v_9217 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2783 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2785) (bv_or (lshr v_9214 (uvalueMInt v_9217)) (extract (shl v_9214 (uvalueMInt (sub (expression.bv_nat 32 32) v_9217))) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2804 : imm int) (v_2805 : reg (bv 64)) (v_2806 : reg (bv 64)) => do
      v_9237 <- getRegister v_2805;
      v_9240 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2804 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2806) (bv_or (lshr v_9237 (uvalueMInt v_9240)) (extract (shl v_9237 (uvalueMInt (sub (expression.bv_nat 64 64) v_9240))) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2773 : imm int) (v_2774 : Mem) (v_2775 : reg (bv 32)) => do
      v_15201 <- evaluateAddress v_2774;
      v_15202 <- load v_15201 4;
      v_15205 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2773 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2775) (bv_or (lshr v_15202 (uvalueMInt v_15205)) (extract (shl v_15202 (uvalueMInt (sub (expression.bv_nat 32 32) v_15205))) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2794 : imm int) (v_2796 : Mem) (v_2795 : reg (bv 64)) => do
      v_15214 <- evaluateAddress v_2796;
      v_15215 <- load v_15214 8;
      v_15218 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2794 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2795) (bv_or (lshr v_15215 (uvalueMInt v_15218)) (extract (shl v_15215 (uvalueMInt (sub (expression.bv_nat 64 64) v_15218))) 0 64));
      pure ()
    pat_end
