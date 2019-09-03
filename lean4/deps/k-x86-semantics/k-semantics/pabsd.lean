def pabsd1 : instruction :=
  definst "pabsd" $ do
    pattern fun (v_3069 : reg (bv 128)) (v_3070 : reg (bv 128)) => do
      v_5263 <- getRegister v_3069;
      v_5264 <- eval (extract v_5263 0 32);
      v_5269 <- eval (extract v_5263 32 64);
      v_5274 <- eval (extract v_5263 64 96);
      v_5279 <- eval (extract v_5263 96 128);
      setRegister (lhs.of_reg v_3070) (concat (mux (ugt v_5264 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5264 (expression.bv_nat 32 4294967295))) v_5264) (concat (mux (ugt v_5269 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5269 (expression.bv_nat 32 4294967295))) v_5269) (concat (mux (ugt v_5274 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5274 (expression.bv_nat 32 4294967295))) v_5274) (mux (ugt v_5279 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5279 (expression.bv_nat 32 4294967295))) v_5279))));
      pure ()
    pat_end;
    pattern fun (v_3065 : Mem) (v_3066 : reg (bv 128)) => do
      v_9365 <- evaluateAddress v_3065;
      v_9366 <- load v_9365 16;
      v_9367 <- eval (extract v_9366 0 32);
      v_9372 <- eval (extract v_9366 32 64);
      v_9377 <- eval (extract v_9366 64 96);
      v_9382 <- eval (extract v_9366 96 128);
      setRegister (lhs.of_reg v_3066) (concat (mux (ugt v_9367 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9367 (expression.bv_nat 32 4294967295))) v_9367) (concat (mux (ugt v_9372 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9372 (expression.bv_nat 32 4294967295))) v_9372) (concat (mux (ugt v_9377 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9377 (expression.bv_nat 32 4294967295))) v_9377) (mux (ugt v_9382 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9382 (expression.bv_nat 32 4294967295))) v_9382))));
      pure ()
    pat_end
