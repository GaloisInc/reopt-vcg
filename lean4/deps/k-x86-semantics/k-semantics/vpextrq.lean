def vpextrq1 : instruction :=
  definst "vpextrq" $ do
    pattern fun (v_3212 : imm int) (v_3213 : reg (bv 128)) (v_3215 : reg (bv 64)) => do
      v_8651 <- getRegister v_3213;
      setRegister (lhs.of_reg v_3215) (extract (lshr v_8651 (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3212 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128)) 64 128);
      pure ()
    pat_end;
    pattern fun (v_3208 : imm int) (v_3209 : reg (bv 128)) (v_3207 : Mem) => do
      v_19225 <- evaluateAddress v_3207;
      v_19226 <- getRegister v_3209;
      store v_19225 (extract (lshr v_19226 (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3208 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128)) 64 128) 8;
      pure ()
    pat_end
