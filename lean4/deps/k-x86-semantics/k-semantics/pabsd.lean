def pabsd1 : instruction :=
  definst "pabsd" $ do
    pattern fun (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_5176 <- getRegister v_3120;
      v_5177 <- eval (extract v_5176 0 32);
      v_5182 <- eval (extract v_5176 32 64);
      v_5187 <- eval (extract v_5176 64 96);
      v_5192 <- eval (extract v_5176 96 128);
      setRegister (lhs.of_reg v_3121) (concat (mux (ugt v_5177 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5177 (expression.bv_nat 32 4294967295))) v_5177) (concat (mux (ugt v_5182 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5182 (expression.bv_nat 32 4294967295))) v_5182) (concat (mux (ugt v_5187 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5187 (expression.bv_nat 32 4294967295))) v_5187) (mux (ugt v_5192 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5192 (expression.bv_nat 32 4294967295))) v_5192))));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_9129 <- evaluateAddress v_3115;
      v_9130 <- load v_9129 16;
      v_9131 <- eval (extract v_9130 0 32);
      v_9136 <- eval (extract v_9130 32 64);
      v_9141 <- eval (extract v_9130 64 96);
      v_9146 <- eval (extract v_9130 96 128);
      setRegister (lhs.of_reg v_3116) (concat (mux (ugt v_9131 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9131 (expression.bv_nat 32 4294967295))) v_9131) (concat (mux (ugt v_9136 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9136 (expression.bv_nat 32 4294967295))) v_9136) (concat (mux (ugt v_9141 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9141 (expression.bv_nat 32 4294967295))) v_9141) (mux (ugt v_9146 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_9146 (expression.bv_nat 32 4294967295))) v_9146))));
      pure ()
    pat_end
