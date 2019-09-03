def vpermps1 : instruction :=
  definst "vpermps" $ do
    pattern fun (v_3072 : reg (bv 256)) (v_3073 : reg (bv 256)) (v_3074 : reg (bv 256)) => do
      v_8763 <- getRegister v_3072;
      v_8764 <- getRegister v_3073;
      setRegister (lhs.of_reg v_3074) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_8763 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8764 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3066 : Mem) (v_3067 : reg (bv 256)) (v_3068 : reg (bv 256)) => do
      v_17885 <- evaluateAddress v_3066;
      v_17886 <- load v_17885 32;
      v_17887 <- getRegister v_3067;
      setRegister (lhs.of_reg v_3068) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_17886 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_17887 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end
