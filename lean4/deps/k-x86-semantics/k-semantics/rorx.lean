def rorx1 : instruction :=
  definst "rorx" $ do
    pattern fun (v_2770 : imm int) (v_2773 : reg (bv 32)) (v_2774 : reg (bv 32)) => do
      v_9294 <- getRegister v_2773;
      v_9297 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2770 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2774) (bv_or (lshr v_9294 (uvalueMInt v_9297)) (extract (shl v_9294 (uvalueMInt (sub (expression.bv_nat 32 32) v_9297))) 0 (bitwidthMInt v_9294)));
      pure ()
    pat_end;
    pattern fun (v_2791 : imm int) (v_2794 : reg (bv 64)) (v_2795 : reg (bv 64)) => do
      v_9318 <- getRegister v_2794;
      v_9321 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2791 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2795) (bv_or (lshr v_9318 (uvalueMInt v_9321)) (extract (shl v_9318 (uvalueMInt (sub (expression.bv_nat 64 64) v_9321))) 0 (bitwidthMInt v_9318)));
      pure ()
    pat_end;
    pattern fun (v_2760 : imm int) (v_2763 : Mem) (v_2764 : reg (bv 32)) => do
      v_15383 <- evaluateAddress v_2763;
      v_15384 <- load v_15383 4;
      v_15387 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2760 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2764) (bv_or (lshr v_15384 (uvalueMInt v_15387)) (extract (shl v_15384 (uvalueMInt (sub (expression.bv_nat 32 32) v_15387))) 0 (bitwidthMInt v_15384)));
      pure ()
    pat_end;
    pattern fun (v_2781 : imm int) (v_2784 : Mem) (v_2785 : reg (bv 64)) => do
      v_15397 <- evaluateAddress v_2784;
      v_15398 <- load v_15397 8;
      v_15401 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2781 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2785) (bv_or (lshr v_15398 (uvalueMInt v_15401)) (extract (shl v_15398 (uvalueMInt (sub (expression.bv_nat 64 64) v_15401))) 0 (bitwidthMInt v_15398)));
      pure ()
    pat_end
