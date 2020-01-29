def vpermd : instruction :=
  definst "vpermd" $ do
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 3)) <- eval (extract v_5 29 32);
      (v_7 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_6) (expression.bv_nat 256 32))) 224 256);
      (v_8 : expression (bv 3)) <- eval (extract v_5 61 64);
      (v_9 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_8) (expression.bv_nat 256 32))) 224 256);
      (v_10 : expression (bv 3)) <- eval (extract v_5 93 96);
      (v_11 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_10) (expression.bv_nat 256 32))) 224 256);
      (v_12 : expression (bv 3)) <- eval (extract v_5 125 128);
      (v_13 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_12) (expression.bv_nat 256 32))) 224 256);
      (v_14 : expression (bv 3)) <- eval (extract v_5 157 160);
      (v_15 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_14) (expression.bv_nat 256 32))) 224 256);
      (v_16 : expression (bv 3)) <- eval (extract v_5 189 192);
      (v_17 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_16) (expression.bv_nat 256 32))) 224 256);
      (v_18 : expression (bv 3)) <- eval (extract v_5 221 224);
      (v_19 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_18) (expression.bv_nat 256 32))) 224 256);
      (v_20 : expression (bv 3)) <- eval (extract v_5 253 256);
      (v_21 : expression (bv 32)) <- eval (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) v_20) (expression.bv_nat 256 32))) 224 256);
      setRegister (lhs.of_reg ymm_2) (concat v_7 (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 v_21)))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      (v_5 : expression (bv 3)) <- eval (extract v_4 29 32);
      (v_6 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_5) (expression.bv_nat 256 32))) 224 256);
      (v_7 : expression (bv 3)) <- eval (extract v_4 61 64);
      (v_8 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_7) (expression.bv_nat 256 32))) 224 256);
      (v_9 : expression (bv 3)) <- eval (extract v_4 93 96);
      (v_10 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_9) (expression.bv_nat 256 32))) 224 256);
      (v_11 : expression (bv 3)) <- eval (extract v_4 125 128);
      (v_12 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_11) (expression.bv_nat 256 32))) 224 256);
      (v_13 : expression (bv 3)) <- eval (extract v_4 157 160);
      (v_14 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_13) (expression.bv_nat 256 32))) 224 256);
      (v_15 : expression (bv 3)) <- eval (extract v_4 189 192);
      (v_16 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_15) (expression.bv_nat 256 32))) 224 256);
      (v_17 : expression (bv 3)) <- eval (extract v_4 221 224);
      (v_18 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_17) (expression.bv_nat 256 32))) 224 256);
      (v_19 : expression (bv 3)) <- eval (extract v_4 253 256);
      (v_20 : expression (bv 32)) <- eval (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) v_19) (expression.bv_nat 256 32))) 224 256);
      setRegister (lhs.of_reg ymm_2) (concat v_6 (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 v_20)))))));
      pure ()
    pat_end
