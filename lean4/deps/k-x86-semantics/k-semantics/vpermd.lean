def vpermd1 : instruction :=
  definst "vpermd" $ do
    pattern fun (v_2975 : reg (bv 256)) (v_2976 : reg (bv 256)) (v_2977 : reg (bv 256)) => do
      v_8204 <- getRegister v_2975;
      v_8205 <- getRegister v_2976;
      setRegister (lhs.of_reg v_2977) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_8204 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_8205 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_2969 : Mem) (v_2970 : reg (bv 256)) (v_2971 : reg (bv 256)) => do
      v_16994 <- evaluateAddress v_2969;
      v_16995 <- load v_16994 32;
      v_16996 <- getRegister v_2970;
      setRegister (lhs.of_reg v_2971) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 29 32)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 61 64)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 93 96)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 125 128)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 157 160)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 189 192)) (expression.bv_nat 256 32)))) 224 256) (concat (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 221 224)) (expression.bv_nat 256 32)))) 224 256) (extract (lshr v_16995 (uvalueMInt (mul (concat (expression.bv_nat 253 0) (extract v_16996 253 256)) (expression.bv_nat 256 32)))) 224 256))))))));
      pure ()
    pat_end
