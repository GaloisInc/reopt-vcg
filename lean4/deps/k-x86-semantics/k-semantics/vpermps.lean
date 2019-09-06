def vpermps1 : instruction :=
  definst "vpermps" $ do
    pattern fun (v_3162 : reg (bv 256)) (v_3163 : reg (bv 256)) (v_3164 : reg (bv 256)) => do
      v_8522 <- getRegister v_3162;
      v_8523 <- getRegister v_3163;
      setRegister (lhs.of_reg v_3164) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_8522 (mul (concat (expression.bv_nat 253 0) (extract v_8523 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3157 : Mem) (v_3158 : reg (bv 256)) (v_3159 : reg (bv 256)) => do
      v_17024 <- evaluateAddress v_3157;
      v_17025 <- load v_17024 32;
      v_17026 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3159) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_17025 (mul (concat (expression.bv_nat 253 0) (extract v_17026 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end
