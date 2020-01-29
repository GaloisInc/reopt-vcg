def pshuflw : instruction :=
  definst "pshuflw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_6 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_7 : expression (bv 2)) <- eval (extract v_6 0 2);
      (v_8 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_7) (expression.bv_nat 128 4)) 0 128);
      (v_9 : expression (bv 16)) <- eval (extract (lshr v_4 v_8) 112 128);
      (v_10 : expression (bv 2)) <- eval (extract v_6 2 4);
      (v_11 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_10) (expression.bv_nat 128 4)) 0 128);
      (v_12 : expression (bv 16)) <- eval (extract (lshr v_4 v_11) 112 128);
      (v_13 : expression (bv 2)) <- eval (extract v_6 4 6);
      (v_14 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_13) (expression.bv_nat 128 4)) 0 128);
      (v_15 : expression (bv 16)) <- eval (extract (lshr v_4 v_14) 112 128);
      (v_16 : expression (bv 2)) <- eval (extract v_6 6 8);
      (v_17 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_16) (expression.bv_nat 128 4)) 0 128);
      (v_18 : expression (bv 16)) <- eval (extract (lshr v_4 v_17) 112 128);
      setRegister (lhs.of_reg xmm_2) (concat v_5 (concat v_9 (concat v_12 (concat v_15 v_18))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_6 : expression (bv 2)) <- eval (extract v_5 0 2);
      (v_7 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_6) (expression.bv_nat 128 4)) 0 128);
      (v_8 : expression (bv 16)) <- eval (extract (lshr v_3 v_7) 112 128);
      (v_9 : expression (bv 2)) <- eval (extract v_5 2 4);
      (v_10 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_9) (expression.bv_nat 128 4)) 0 128);
      (v_11 : expression (bv 16)) <- eval (extract (lshr v_3 v_10) 112 128);
      (v_12 : expression (bv 2)) <- eval (extract v_5 4 6);
      (v_13 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_12) (expression.bv_nat 128 4)) 0 128);
      (v_14 : expression (bv 16)) <- eval (extract (lshr v_3 v_13) 112 128);
      (v_15 : expression (bv 2)) <- eval (extract v_5 6 8);
      (v_16 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_15) (expression.bv_nat 128 4)) 0 128);
      (v_17 : expression (bv 16)) <- eval (extract (lshr v_3 v_16) 112 128);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (concat v_8 (concat v_11 (concat v_14 v_17))));
      pure ()
    pat_end
