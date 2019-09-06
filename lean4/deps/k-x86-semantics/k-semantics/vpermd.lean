def vpermd1 : instruction :=
  definst "vpermd" $ do
    pattern fun (v_3052 : reg (bv 256)) (v_3053 : reg (bv 256)) (v_3054 : reg (bv 256)) => do
      v_8128 <- getRegister v_3052;
      v_8129 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3054) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_8128 (mul (concat (expression.bv_nat 253 0) (extract v_8129 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3047 : Mem) (v_3048 : reg (bv 256)) (v_3049 : reg (bv 256)) => do
      v_16670 <- evaluateAddress v_3047;
      v_16671 <- load v_16670 32;
      v_16672 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3049) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_16671 (mul (concat (expression.bv_nat 253 0) (extract v_16672 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end
