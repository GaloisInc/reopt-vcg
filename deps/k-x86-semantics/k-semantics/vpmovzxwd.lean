def vpmovzxwd : instruction :=
  definst "vpmovzxwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 16 0) (concat v_4 (concat (expression.bv_nat 16 0) (concat v_5 (concat (expression.bv_nat 16 0) (concat v_6 (concat (expression.bv_nat 16 0) v_7)))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg ymm_1) (concat (expression.bv_nat 16 0) (concat v_4 (concat (expression.bv_nat 16 0) (concat v_5 (concat (expression.bv_nat 16 0) (concat v_6 (concat (expression.bv_nat 16 0) (concat v_7 (concat (expression.bv_nat 16 0) (concat v_8 (concat (expression.bv_nat 16 0) (concat v_9 (concat (expression.bv_nat 16 0) (concat v_10 (concat (expression.bv_nat 16 0) v_11)))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_4 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_5 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 16 0) (concat v_3 (concat (expression.bv_nat 16 0) (concat v_4 (concat (expression.bv_nat 16 0) (concat v_5 (concat (expression.bv_nat 16 0) v_6)))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      setRegister (lhs.of_reg ymm_1) (concat (expression.bv_nat 16 0) (concat v_3 (concat (expression.bv_nat 16 0) (concat v_4 (concat (expression.bv_nat 16 0) (concat v_5 (concat (expression.bv_nat 16 0) (concat v_6 (concat (expression.bv_nat 16 0) (concat v_7 (concat (expression.bv_nat 16 0) (concat v_8 (concat (expression.bv_nat 16 0) (concat v_9 (concat (expression.bv_nat 16 0) v_10)))))))))))))));
      pure ()
    pat_end
