def pabsd1 : instruction :=
  definst "pabsd" $ do
    pattern fun (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) => do
      v_5208 <- getRegister v_3057;
      v_5209 <- eval (extract v_5208 0 32);
      v_5216 <- eval (extract v_5208 32 64);
      v_5223 <- eval (extract v_5208 64 96);
      v_5230 <- eval (extract v_5208 96 128);
      setRegister (lhs.of_reg v_3058) (concat (mux (ugt v_5209 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5209 (mi (bitwidthMInt v_5209) -1))) v_5209) (concat (mux (ugt v_5216 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5216 (mi (bitwidthMInt v_5216) -1))) v_5216) (concat (mux (ugt v_5223 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5223 (mi (bitwidthMInt v_5223) -1))) v_5223) (mux (ugt v_5230 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5230 (mi (bitwidthMInt v_5230) -1))) v_5230))));
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 128)) => do
      v_9322 <- evaluateAddress v_3052;
      v_9323 <- load v_9322 16;
      v_9324 <- eval (extract v_9323 0 32);
      v_9331 <- eval (extract v_9323 32 64);
      v_9338 <- eval (extract v_9323 64 96);
      v_9345 <- eval (extract v_9323 96 128);
      setRegister (lhs.of_reg v_3053) (concat (mux (ugt v_9324 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9324 (mi (bitwidthMInt v_9324) -1))) v_9324) (concat (mux (ugt v_9331 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9331 (mi (bitwidthMInt v_9331) -1))) v_9331) (concat (mux (ugt v_9338 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9338 (mi (bitwidthMInt v_9338) -1))) v_9338) (mux (ugt v_9345 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9345 (mi (bitwidthMInt v_9345) -1))) v_9345))));
      pure ()
    pat_end
