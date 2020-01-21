def vpsrlq : instruction :=
  definst "vpsrlq" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_4 0 64) v_3) (lshr (extract v_4 64 128) v_3)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      v_4 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_4 0 64) v_3) (concat (lshr (extract v_4 64 128) v_3) (concat (lshr (extract v_4 128 192) v_3) (lshr (extract v_4 192 256) v_3)))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_6 0 64) v_5) (lshr (extract v_6 64 128) v_5)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_6 0 64) v_5) (concat (lshr (extract v_6 64 128) v_5) (concat (lshr (extract v_6 128 192) v_5) (lshr (extract v_6 192 256) v_5)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_5 0 64) v_4) (lshr (extract v_5 64 128) v_4)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_5 0 64) v_4) (concat (lshr (extract v_5 64 128) v_4) (concat (lshr (extract v_5 128 192) v_4) (lshr (extract v_5 192 256) v_4)))));
      pure ()
    pat_end
