def pshufhw : instruction :=
  definst "pshufhw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 16;
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 126 0) (extract v_5 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 126 0) (extract v_5 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 126 0) (extract v_5 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_4 (extract (shl (concat (expression.bv_nat 126 0) (extract v_5 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_4 64 128)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      setRegister (lhs.of_reg xmm_2) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract v_4 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract v_4 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract v_4 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_3 (extract (shl (concat (expression.bv_nat 126 0) (extract v_4 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_3 64 128)))));
      pure ()
    pat_end
