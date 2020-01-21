def vpalignr : instruction :=
  definst "vpalignr" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      setRegister (lhs.of_reg xmm_3) (extract (lshr (concat v_4 v_6) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 32;
      v_7 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg ymm_3) (concat (extract (lshr (concat (extract v_4 0 128) (extract v_6 0 128)) v_7) 128 256) (extract (lshr (concat (extract v_4 128 256) (extract v_6 128 256)) v_7) 128 256));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_3) (extract (lshr (concat v_4 v_5) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_2);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      v_6 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg ymm_3) (concat (extract (lshr (concat (extract v_4 0 128) (extract v_5 0 128)) v_6) 128 256) (extract (lshr (concat (extract v_4 128 256) (extract v_5 128 256)) v_6) 128 256));
      pure ()
    pat_end
