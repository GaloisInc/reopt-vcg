def pabsd1 : instruction :=
  definst "pabsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 0 32);
      v_5 <- eval (extract v_3 32 64);
      v_6 <- eval (extract v_3 64 96);
      v_7 <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_4 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_4 (expression.bv_nat 32 4294967295))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5 (expression.bv_nat 32 4294967295))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6 (expression.bv_nat 32 4294967295))) v_6) (mux (ugt v_7 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_7 (expression.bv_nat 32 4294967295))) v_7))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 0 32);
      v_4 <- eval (extract v_2 32 64);
      v_5 <- eval (extract v_2 64 96);
      v_6 <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_3 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_3 (expression.bv_nat 32 4294967295))) v_3) (concat (mux (ugt v_4 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_4 (expression.bv_nat 32 4294967295))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5 (expression.bv_nat 32 4294967295))) v_5) (mux (ugt v_6 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_6 (expression.bv_nat 32 4294967295))) v_6))));
      pure ()
    pat_end
