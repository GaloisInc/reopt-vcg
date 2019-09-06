def pabsd1 : instruction :=
  definst "pabsd" $ do
    pattern fun (v_3145 : reg (bv 128)) (v_3146 : reg (bv 128)) => do
      v_5203 <- getRegister v_3145;
      v_5204 <- eval (extract v_5203 0 32);
      v_5209 <- eval (extract v_5203 32 64);
      v_5214 <- eval (extract v_5203 64 96);
      v_5219 <- eval (extract v_5203 96 128);
      setRegister (lhs.of_reg v_3146) (concat (mux (ugt v_5204 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5204 (expression.bv_nat 32 4294967295))) v_5204) (concat (mux (ugt v_5209 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5209 (expression.bv_nat 32 4294967295))) v_5209) (concat (mux (ugt v_5214 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5214 (expression.bv_nat 32 4294967295))) v_5214) (mux (ugt v_5219 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5219 (expression.bv_nat 32 4294967295))) v_5219))));
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) (v_3142 : reg (bv 128)) => do
      v_9156 <- evaluateAddress v_3141;
      v_9157 <- load v_9156 16;
      v_9158 <- eval (extract v_9157 0 32);
      v_9163 <- eval (extract v_9157 32 64);
      v_9168 <- eval (extract v_9157 64 96);
      v_9173 <- eval (extract v_9157 96 128);
      setRegister (lhs.of_reg v_3142) (concat (mux (ugt v_9158 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9158 (expression.bv_nat 32 4294967295))) v_9158) (concat (mux (ugt v_9163 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9163 (expression.bv_nat 32 4294967295))) v_9163) (concat (mux (ugt v_9168 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9168 (expression.bv_nat 32 4294967295))) v_9168) (mux (ugt v_9173 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9173 (expression.bv_nat 32 4294967295))) v_9173))));
      pure ()
    pat_end
