def vpextrd1 : instruction :=
  definst "vpextrd" $ do
    pattern fun (v_3201 : imm int) (v_3202 : reg (bv 128)) (v_3203 : reg (bv 32)) => do
      v_8637 <- getRegister v_3202;
      setRegister (lhs.of_reg v_3203) (extract (lshr v_8637 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3201 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_3197 : imm int) (v_3198 : reg (bv 128)) (v_3196 : Mem) => do
      v_19215 <- evaluateAddress v_3196;
      v_19216 <- getRegister v_3198;
      store v_19215 (extract (lshr v_19216 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3197 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
