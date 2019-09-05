def vpextrq1 : instruction :=
  definst "vpextrq" $ do
    pattern fun (v_3185 : imm int) (v_3188 : reg (bv 128)) (v_3186 : reg (bv 64)) => do
      v_8624 <- getRegister v_3188;
      setRegister (lhs.of_reg v_3186) (extract (lshr v_8624 (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3185 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128)) 64 128);
      pure ()
    pat_end;
    pattern fun (v_3180 : imm int) (v_3182 : reg (bv 128)) (v_3181 : Mem) => do
      v_19198 <- evaluateAddress v_3181;
      v_19199 <- getRegister v_3182;
      store v_19198 (extract (lshr v_19199 (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3180 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128)) 64 128) 8;
      pure ()
    pat_end
