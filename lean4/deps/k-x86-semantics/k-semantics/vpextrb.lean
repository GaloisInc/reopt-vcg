def vpextrb1 : instruction :=
  definst "vpextrb" $ do
    pattern fun (v_3157 : imm int) (v_3159 : reg (bv 128)) (v_3160 : reg (bv 32)) => do
      v_8585 <- getRegister v_3159;
      setRegister (lhs.of_reg v_3160) (concat (expression.bv_nat 24 0) (extract (lshr v_8585 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3157 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3163 : imm int) (v_3166 : reg (bv 128)) (v_3164 : reg (bv 64)) => do
      v_8595 <- getRegister v_3166;
      setRegister (lhs.of_reg v_3164) (concat (expression.bv_nat 56 0) (extract (lshr v_8595 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3163 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3152 : imm int) (v_3154 : reg (bv 128)) (v_3153 : Mem) => do
      v_19178 <- evaluateAddress v_3153;
      v_19179 <- getRegister v_3154;
      store v_19178 (extract (lshr v_19179 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3152 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128) 1;
      pure ()
    pat_end
