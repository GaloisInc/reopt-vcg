def vpermps : instruction :=
  definst "vpermps" $ do
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_4 (mul (concat (expression.bv_nat 253 0) (extract v_5 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_3 (mul (concat (expression.bv_nat 253 0) (extract v_4 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end
