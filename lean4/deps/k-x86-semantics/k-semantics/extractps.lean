def extractps1 : instruction :=
  definst "extractps" $ do
    pattern fun (v_2799 : imm int) (v_2798 : reg (bv 128)) (v_2800 : reg (bv 32)) => do
      v_4764 <- getRegister v_2798;
      v_4767 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2799 8 8) 6 8));
      setRegister (lhs.of_reg v_2800) (extract (lshr v_4764 (uvalueMInt (extract (shl v_4767 5) 0 (bitwidthMInt v_4767)))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2806 : imm int) (v_2805 : reg (bv 128)) (v_2804 : reg (bv 64)) => do
      v_4775 <- getRegister v_2805;
      v_4778 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2806 8 8) 6 8));
      setRegister (lhs.of_reg v_2804) (concat (expression.bv_nat 32 0) (extract (lshr v_4775 (uvalueMInt (extract (shl v_4778 5) 0 (bitwidthMInt v_4778)))) 96 128));
      pure ()
    pat_end;
    pattern fun (v_2795 : imm int) (v_2794 : reg (bv 128)) (v_2793 : Mem) => do
      v_9507 <- evaluateAddress v_2793;
      v_9508 <- getRegister v_2794;
      v_9511 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2795 8 8) 6 8));
      store v_9507 (extract (lshr v_9508 (uvalueMInt (extract (shl v_9511 5) 0 (bitwidthMInt v_9511)))) 96 128) 4;
      pure ()
    pat_end
