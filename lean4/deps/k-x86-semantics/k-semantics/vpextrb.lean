def vpextrb1 : instruction :=
  definst "vpextrb" $ do
    pattern fun (v_3184 : imm int) (v_3185 : reg (bv 128)) (v_3186 : reg (bv 32)) => do
      v_8612 <- getRegister v_3185;
      setRegister (lhs.of_reg v_3186) (concat (expression.bv_nat 24 0) (extract (lshr v_8612 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3184 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3190 : imm int) (v_3191 : reg (bv 128)) (v_3193 : reg (bv 64)) => do
      v_8622 <- getRegister v_3191;
      setRegister (lhs.of_reg v_3193) (concat (expression.bv_nat 56 0) (extract (lshr v_8622 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3190 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128));
      pure ()
    pat_end;
    pattern fun (v_3180 : imm int) (v_3181 : reg (bv 128)) (v_3179 : Mem) => do
      v_19205 <- evaluateAddress v_3179;
      v_19206 <- getRegister v_3181;
      store v_19205 (extract (lshr v_19206 (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_3180 8 8) 4 8)) (expression.bv_nat 128 3)) 0 128)) 120 128) 1;
      pure ()
    pat_end
