def psrlw : instruction :=
  definst "psrlw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (concat (expression.bv_nat 8 0) v_2);
      (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_7 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_8 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_9 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_10 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_11 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_12 : expression (bv 16)) <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (concat (expression.bv_nat 56 0) v_2) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr v_4 v_5) (concat (lshr v_6 v_5) (concat (lshr v_7 v_5) (concat (lshr v_8 v_5) (concat (lshr v_9 v_5) (concat (lshr v_10 v_5) (concat (lshr v_11 v_5) (lshr v_12 v_5)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_11 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_12 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_13 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_14 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr v_6 v_7) (concat (lshr v_8 v_7) (concat (lshr v_9 v_7) (concat (lshr v_10 v_7) (concat (lshr v_11 v_7) (concat (lshr v_12 v_7) (concat (lshr v_13 v_7) (lshr v_14 v_7)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_7 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_9 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_10 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_11 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_12 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_13 : expression (bv 16)) <- eval (extract v_4 112 128);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr v_5 v_6) (concat (lshr v_7 v_6) (concat (lshr v_8 v_6) (concat (lshr v_9 v_6) (concat (lshr v_10 v_6) (concat (lshr v_11 v_6) (concat (lshr v_12 v_6) (lshr v_13 v_6)))))))));
      pure ()
    pat_end
