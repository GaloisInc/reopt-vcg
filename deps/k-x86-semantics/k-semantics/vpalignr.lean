def vpalignr : instruction :=
  definst "vpalignr" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_8 : expression (bv 128)) <- eval (extract (lshr (concat v_4 v_6) v_7) 128 256);
      setRegister (lhs.of_reg xmm_3) v_8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      (v_8 : expression (bv 128)) <- eval (extract v_7 0 128);
      (v_9 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_10 : expression (bv 128)) <- eval (extract (lshr (concat v_5 v_8) v_9) 128 256);
      (v_11 : expression (bv 128)) <- eval (extract v_4 128 256);
      (v_12 : expression (bv 128)) <- eval (extract v_7 128 256);
      (v_13 : expression (bv 128)) <- eval (extract (lshr (concat v_11 v_12) v_9) 128 256);
      setRegister (lhs.of_reg ymm_3) (concat v_10 v_13);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_7 : expression (bv 128)) <- eval (extract (lshr (concat v_4 v_5) v_6) 128 256);
      setRegister (lhs.of_reg xmm_3) v_7;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 128)) <- eval (extract v_6 0 128);
      (v_8 : expression (bv 256)) <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      (v_9 : expression (bv 128)) <- eval (extract (lshr (concat v_5 v_7) v_8) 128 256);
      (v_10 : expression (bv 128)) <- eval (extract v_4 128 256);
      (v_11 : expression (bv 128)) <- eval (extract v_6 128 256);
      (v_12 : expression (bv 128)) <- eval (extract (lshr (concat v_10 v_11) v_8) 128 256);
      setRegister (lhs.of_reg ymm_3) (concat v_9 v_12);
      pure ()
    pat_end
