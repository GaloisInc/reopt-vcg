def pshufhw : instruction :=
  definst "pshufhw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 16;
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_6 : expression (bv 2)) <- eval (extract v_5 0 2);
      (v_7 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_6) (expression.bv_nat 128 4)) 0 128);
      (v_8 : expression (bv 16)) <- eval (extract (lshr v_4 v_7) 48 64);
      (v_9 : expression (bv 2)) <- eval (extract v_5 2 4);
      (v_10 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_9) (expression.bv_nat 128 4)) 0 128);
      (v_11 : expression (bv 16)) <- eval (extract (lshr v_4 v_10) 48 64);
      (v_12 : expression (bv 2)) <- eval (extract v_5 4 6);
      (v_13 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_12) (expression.bv_nat 128 4)) 0 128);
      (v_14 : expression (bv 16)) <- eval (extract (lshr v_4 v_13) 48 64);
      (v_15 : expression (bv 2)) <- eval (extract v_5 6 8);
      (v_16 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_15) (expression.bv_nat 128 4)) 0 128);
      (v_17 : expression (bv 16)) <- eval (extract (lshr v_4 v_16) 48 64);
      (v_18 : expression (bv 64)) <- eval (extract v_4 64 128);
      setRegister (lhs.of_reg xmm_2) (concat v_8 (concat v_11 (concat v_14 (concat v_17 v_18))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_5 : expression (bv 2)) <- eval (extract v_4 0 2);
      (v_6 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_5) (expression.bv_nat 128 4)) 0 128);
      (v_7 : expression (bv 16)) <- eval (extract (lshr v_3 v_6) 48 64);
      (v_8 : expression (bv 2)) <- eval (extract v_4 2 4);
      (v_9 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_8) (expression.bv_nat 128 4)) 0 128);
      (v_10 : expression (bv 16)) <- eval (extract (lshr v_3 v_9) 48 64);
      (v_11 : expression (bv 2)) <- eval (extract v_4 4 6);
      (v_12 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_11) (expression.bv_nat 128 4)) 0 128);
      (v_13 : expression (bv 16)) <- eval (extract (lshr v_3 v_12) 48 64);
      (v_14 : expression (bv 2)) <- eval (extract v_4 6 8);
      (v_15 : expression (bv 128)) <- eval (extract (shl (concat (expression.bv_nat 126 0) v_14) (expression.bv_nat 128 4)) 0 128);
      (v_16 : expression (bv 16)) <- eval (extract (lshr v_3 v_15) 48 64);
      (v_17 : expression (bv 64)) <- eval (extract v_3 64 128);
      setRegister (lhs.of_reg xmm_2) (concat v_7 (concat v_10 (concat v_13 (concat v_16 v_17))));
      pure ()
    pat_end
