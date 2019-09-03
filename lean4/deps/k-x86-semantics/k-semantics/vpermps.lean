def vpermps1 : instruction :=
  definst "vpermps" $ do
    pattern fun (v_3085 : reg (bv 256)) (v_3086 : reg (bv 256)) (v_3087 : reg (bv 256)) => do
      v_8622 <- getRegister v_3085;
      v_8623 <- getRegister v_3086;
      setRegister (lhs.of_reg v_3087) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_8622 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8623 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) (v_3080 : reg (bv 256)) (v_3081 : reg (bv 256)) => do
      v_17372 <- evaluateAddress v_3079;
      v_17373 <- load v_17372 32;
      v_17374 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3081) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_17373 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17374 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end
