def extractps1 : instruction :=
  definst "extractps" $ do
    pattern fun (v_2889 : imm int) (v_2891 : reg (bv 128)) (v_2890 : reg (bv 32)) => do
      v_4766 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2890) (extract (lshr v_4766 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2889 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2895 : imm int) (v_2896 : reg (bv 128)) (v_2897 : reg (bv 64)) => do
      v_4775 <- getRegister v_2896;
      setRegister (lhs.of_reg v_2897) (concat (expression.bv_nat 32 0) (extract (lshr v_4775 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2895 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128));
      pure ()
    pat_end;
    pattern fun (v_2884 : imm int) (v_2886 : reg (bv 128)) (v_2885 : Mem) => do
      v_9143 <- evaluateAddress v_2885;
      v_9144 <- getRegister v_2886;
      store v_9143 (extract (lshr v_9144 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2884 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
