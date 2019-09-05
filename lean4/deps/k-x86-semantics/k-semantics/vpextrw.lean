def vpextrw1 : instruction :=
  definst "vpextrw" $ do
    pattern fun (v_3196 : imm int) (v_3198 : reg (bv 128)) (v_3199 : reg (bv 32)) => do
      v_8638 <- getRegister v_3198;
      setRegister (lhs.of_reg v_3199) (concat (expression.bv_nat 16 0) (extract (lshr v_8638 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3196 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3202 : imm int) (v_3205 : reg (bv 128)) (v_3203 : reg (bv 64)) => do
      v_8648 <- getRegister v_3205;
      setRegister (lhs.of_reg v_3203) (concat (expression.bv_nat 48 0) (extract (lshr v_8648 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3202 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3191 : imm int) (v_3193 : reg (bv 128)) (v_3192 : Mem) => do
      v_19208 <- evaluateAddress v_3192;
      v_19209 <- getRegister v_3193;
      store v_19208 (extract (lshr v_19209 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3191 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128) 2;
      pure ()
    pat_end
