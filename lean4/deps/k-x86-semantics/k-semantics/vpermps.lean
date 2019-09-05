def vpermps1 : instruction :=
  definst "vpermps" $ do
    pattern fun (v_3135 : reg (bv 256)) (v_3136 : reg (bv 256)) (v_3137 : reg (bv 256)) => do
      v_8495 <- getRegister v_3135;
      v_8496 <- getRegister v_3136;
      setRegister (lhs.of_reg v_3137) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_8495 (mul (concat (expression.bv_nat 253 0) (extract v_8496 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3130 : Mem) (v_3131 : reg (bv 256)) (v_3132 : reg (bv 256)) => do
      v_16997 <- evaluateAddress v_3130;
      v_16998 <- load v_16997 32;
      v_16999 <- getRegister v_3131;
      setRegister (lhs.of_reg v_3132) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_16998 (mul (concat (expression.bv_nat 253 0) (extract v_16999 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end
