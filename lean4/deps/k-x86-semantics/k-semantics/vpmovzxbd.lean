def vpmovzxbd : instruction :=
  definst "vpmovzxbd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 24 0) (concat v_4 (concat (expression.bv_nat 24 0) (concat v_5 (concat (expression.bv_nat 24 0) (concat v_6 (concat (expression.bv_nat 24 0) v_7)))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      setRegister (lhs.of_reg ymm_1) (concat (expression.bv_nat 24 0) (concat v_4 (concat (expression.bv_nat 24 0) (concat v_5 (concat (expression.bv_nat 24 0) (concat v_6 (concat (expression.bv_nat 24 0) (concat v_7 (concat (expression.bv_nat 24 0) (concat v_8 (concat (expression.bv_nat 24 0) (concat v_9 (concat (expression.bv_nat 24 0) (concat v_10 (concat (expression.bv_nat 24 0) v_11)))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_4 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_5 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_6 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 24 0) (concat v_3 (concat (expression.bv_nat 24 0) (concat v_4 (concat (expression.bv_nat 24 0) (concat v_5 (concat (expression.bv_nat 24 0) v_6)))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_4 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_5 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_6 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_7 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_8 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_9 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_10 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg ymm_1) (concat (expression.bv_nat 24 0) (concat v_3 (concat (expression.bv_nat 24 0) (concat v_4 (concat (expression.bv_nat 24 0) (concat v_5 (concat (expression.bv_nat 24 0) (concat v_6 (concat (expression.bv_nat 24 0) (concat v_7 (concat (expression.bv_nat 24 0) (concat v_8 (concat (expression.bv_nat 24 0) (concat v_9 (concat (expression.bv_nat 24 0) v_10)))))))))))))));
      pure ()
    pat_end
