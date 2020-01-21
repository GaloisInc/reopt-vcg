def vpermq : instruction :=
  definst "vpermq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 32;
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg ymm_2) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 254 0) (extract v_5 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 254 0) (extract v_5 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 254 0) (extract v_5 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 254 0) (extract v_5 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg ymm_2) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 254 0) (extract v_4 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 254 0) (extract v_4 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 254 0) (extract v_4 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 254 0) (extract v_4 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end
