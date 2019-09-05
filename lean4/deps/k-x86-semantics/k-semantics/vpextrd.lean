def vpextrd1 : instruction :=
  definst "vpextrd" $ do
    pattern fun (v_3174 : imm int) (v_3176 : reg (bv 128)) (v_3177 : reg (bv 32)) => do
      v_8610 <- getRegister v_3176;
      setRegister (lhs.of_reg v_3177) (extract (lshr v_8610 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3174 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_3169 : imm int) (v_3171 : reg (bv 128)) (v_3170 : Mem) => do
      v_19188 <- evaluateAddress v_3170;
      v_19189 <- getRegister v_3171;
      store v_19188 (extract (lshr v_19189 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3169 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
