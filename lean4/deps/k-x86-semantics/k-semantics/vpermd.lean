def vpermd1 : instruction :=
  definst "vpermd" $ do
    pattern fun (v_3025 : reg (bv 256)) (v_3026 : reg (bv 256)) (v_3027 : reg (bv 256)) => do
      v_8101 <- getRegister v_3025;
      v_8102 <- getRegister v_3026;
      setRegister (lhs.of_reg v_3027) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_8101 (mul (concat (expression.bv_nat 253 0) (extract v_8102 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3020 : Mem) (v_3021 : reg (bv 256)) (v_3022 : reg (bv 256)) => do
      v_16643 <- evaluateAddress v_3020;
      v_16644 <- load v_16643 32;
      v_16645 <- getRegister v_3021;
      setRegister (lhs.of_reg v_3022) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 29 32)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 61 64)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 93 96)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 125 128)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 157 160)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 189 192)) (expression.bv_nat 256 32))) 224 256) (concat (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 221 224)) (expression.bv_nat 256 32))) 224 256) (extract (lshr v_16644 (mul (concat (expression.bv_nat 253 0) (extract v_16645 253 256)) (expression.bv_nat 256 32))) 224 256))))))));
      pure ()
    pat_end
