def vpmuludq : instruction :=
  definst "vpmuludq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_7)) (mul (concat (expression.bv_nat 32 0) v_8) (concat (expression.bv_nat 32 0) v_9)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_10 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_11 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_12 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_13 : expression (bv 32)) <- eval (extract v_6 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_7)) (concat (mul (concat (expression.bv_nat 32 0) v_8) (concat (expression.bv_nat 32 0) v_9)) (concat (mul (concat (expression.bv_nat 32 0) v_10) (concat (expression.bv_nat 32 0) v_11)) (mul (concat (expression.bv_nat 32 0) v_12) (concat (expression.bv_nat 32 0) v_13)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_6)) (mul (concat (expression.bv_nat 32 0) v_7) (concat (expression.bv_nat 32 0) v_8)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_10 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_11 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_12 : expression (bv 32)) <- eval (extract v_5 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mul (concat (expression.bv_nat 32 0) v_4) (concat (expression.bv_nat 32 0) v_6)) (concat (mul (concat (expression.bv_nat 32 0) v_7) (concat (expression.bv_nat 32 0) v_8)) (concat (mul (concat (expression.bv_nat 32 0) v_9) (concat (expression.bv_nat 32 0) v_10)) (mul (concat (expression.bv_nat 32 0) v_11) (concat (expression.bv_nat 32 0) v_12)))));
      pure ()
    pat_end
