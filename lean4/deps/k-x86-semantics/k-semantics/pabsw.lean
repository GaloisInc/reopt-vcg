def pabsw1 : instruction :=
  definst "pabsw" $ do
    pattern fun (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) => do
      v_5205 <- getRegister v_3129;
      v_5206 <- eval (extract v_5205 0 16);
      v_5211 <- eval (extract v_5205 16 32);
      v_5216 <- eval (extract v_5205 32 48);
      v_5221 <- eval (extract v_5205 48 64);
      v_5226 <- eval (extract v_5205 64 80);
      v_5231 <- eval (extract v_5205 80 96);
      v_5236 <- eval (extract v_5205 96 112);
      v_5241 <- eval (extract v_5205 112 128);
      setRegister (lhs.of_reg v_3130) (concat (mux (ugt v_5206 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5206 (expression.bv_nat 16 65535))) v_5206) (concat (mux (ugt v_5211 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5211 (expression.bv_nat 16 65535))) v_5211) (concat (mux (ugt v_5216 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5216 (expression.bv_nat 16 65535))) v_5216) (concat (mux (ugt v_5221 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5221 (expression.bv_nat 16 65535))) v_5221) (concat (mux (ugt v_5226 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5226 (expression.bv_nat 16 65535))) v_5226) (concat (mux (ugt v_5231 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5231 (expression.bv_nat 16 65535))) v_5231) (concat (mux (ugt v_5236 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5236 (expression.bv_nat 16 65535))) v_5236) (mux (ugt v_5241 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5241 (expression.bv_nat 16 65535))) v_5241))))))));
      pure ()
    pat_end;
    pattern fun (v_3124 : Mem) (v_3125 : reg (bv 128)) => do
      v_9155 <- evaluateAddress v_3124;
      v_9156 <- load v_9155 16;
      v_9157 <- eval (extract v_9156 0 16);
      v_9162 <- eval (extract v_9156 16 32);
      v_9167 <- eval (extract v_9156 32 48);
      v_9172 <- eval (extract v_9156 48 64);
      v_9177 <- eval (extract v_9156 64 80);
      v_9182 <- eval (extract v_9156 80 96);
      v_9187 <- eval (extract v_9156 96 112);
      v_9192 <- eval (extract v_9156 112 128);
      setRegister (lhs.of_reg v_3125) (concat (mux (ugt v_9157 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9157 (expression.bv_nat 16 65535))) v_9157) (concat (mux (ugt v_9162 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9162 (expression.bv_nat 16 65535))) v_9162) (concat (mux (ugt v_9167 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9167 (expression.bv_nat 16 65535))) v_9167) (concat (mux (ugt v_9172 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9172 (expression.bv_nat 16 65535))) v_9172) (concat (mux (ugt v_9177 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9177 (expression.bv_nat 16 65535))) v_9177) (concat (mux (ugt v_9182 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9182 (expression.bv_nat 16 65535))) v_9182) (concat (mux (ugt v_9187 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9187 (expression.bv_nat 16 65535))) v_9187) (mux (ugt v_9192 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9192 (expression.bv_nat 16 65535))) v_9192))))))));
      pure ()
    pat_end
