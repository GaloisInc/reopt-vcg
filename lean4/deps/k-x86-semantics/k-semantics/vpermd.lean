def vpermd1 : instruction :=
  definst "vpermd" $ do
    pattern fun (v_2962 : reg (bv 256)) (v_2963 : reg (bv 256)) (v_2964 : reg (bv 256)) => do
      v_8341 <- getRegister v_2962;
      v_8342 <- getRegister v_2963;
      setRegister (lhs.of_reg v_2964) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_8341 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8342 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_2956 : Mem) (v_2957 : reg (bv 256)) (v_2958 : reg (bv 256)) => do
      v_17503 <- evaluateAddress v_2956;
      v_17504 <- load v_17503 32;
      v_17505 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2958) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_17504 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17505 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end
