def vpermpd : instruction :=
  definst "vpermpd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 32;
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_6 : expression (bv 2)) <- eval (extract v_5 0 2);
      (v_7 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_6) (expression.bv_nat 256 6)) 0 256);
      (v_8 : expression (bv 64)) <- eval (extract (lshr v_4 v_7) 192 256);
      (v_9 : expression (bv 2)) <- eval (extract v_5 2 4);
      (v_10 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_9) (expression.bv_nat 256 6)) 0 256);
      (v_11 : expression (bv 64)) <- eval (extract (lshr v_4 v_10) 192 256);
      (v_12 : expression (bv 2)) <- eval (extract v_5 4 6);
      (v_13 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_12) (expression.bv_nat 256 6)) 0 256);
      (v_14 : expression (bv 64)) <- eval (extract (lshr v_4 v_13) 192 256);
      (v_15 : expression (bv 2)) <- eval (extract v_5 6 8);
      (v_16 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_15) (expression.bv_nat 256 6)) 0 256);
      (v_17 : expression (bv 64)) <- eval (extract (lshr v_4 v_16) 192 256);
      setRegister (lhs.of_reg ymm_2) (concat v_8 (concat v_11 (concat v_14 v_17)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_5 : expression (bv 2)) <- eval (extract v_4 0 2);
      (v_6 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_5) (expression.bv_nat 256 6)) 0 256);
      (v_7 : expression (bv 64)) <- eval (extract (lshr v_3 v_6) 192 256);
      (v_8 : expression (bv 2)) <- eval (extract v_4 2 4);
      (v_9 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_8) (expression.bv_nat 256 6)) 0 256);
      (v_10 : expression (bv 64)) <- eval (extract (lshr v_3 v_9) 192 256);
      (v_11 : expression (bv 2)) <- eval (extract v_4 4 6);
      (v_12 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_11) (expression.bv_nat 256 6)) 0 256);
      (v_13 : expression (bv 64)) <- eval (extract (lshr v_3 v_12) 192 256);
      (v_14 : expression (bv 2)) <- eval (extract v_4 6 8);
      (v_15 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 254 0) v_14) (expression.bv_nat 256 6)) 0 256);
      (v_16 : expression (bv 64)) <- eval (extract (lshr v_3 v_15) 192 256);
      setRegister (lhs.of_reg ymm_2) (concat v_7 (concat v_10 (concat v_13 v_16)));
      pure ()
    pat_end
