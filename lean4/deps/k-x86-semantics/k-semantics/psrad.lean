def psrad : instruction :=
  definst "psrad" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_4) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_8 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (ashr v_3 v_5) (concat (ashr v_6 v_5) (concat (ashr v_7 v_5) (ashr v_8 v_5))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (ashr v_3 v_8) (concat (ashr v_9 v_8) (concat (ashr v_10 v_8) (ashr v_11 v_8))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      (v_6 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_7 <- eval (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_6);
      (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (ashr v_3 v_7) (concat (ashr v_8 v_7) (concat (ashr v_9 v_7) (ashr v_10 v_7))));
      pure ()
    pat_end
