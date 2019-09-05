def extractps1 : instruction :=
  definst "extractps" $ do
    pattern fun (v_2862 : imm int) (v_2865 : reg (bv 128)) (v_2864 : reg (bv 32)) => do
      v_4745 <- getRegister v_2865;
      setRegister (lhs.of_reg v_2864) (extract (lshr v_4745 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2862 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2868 : imm int) (v_2871 : reg (bv 128)) (v_2869 : reg (bv 64)) => do
      v_4754 <- getRegister v_2871;
      setRegister (lhs.of_reg v_2869) (concat (expression.bv_nat 32 0) (extract (lshr v_4754 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2868 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128));
      pure ()
    pat_end;
    pattern fun (v_2858 : imm int) (v_2859 : reg (bv 128)) (v_2857 : Mem) => do
      v_9133 <- evaluateAddress v_2857;
      v_9134 <- getRegister v_2859;
      store v_9133 (extract (lshr v_9134 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2858 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
