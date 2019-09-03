def pabsw1 : instruction :=
  definst "pabsw" $ do
    pattern fun (v_3066 : reg (bv 128)) (v_3067 : reg (bv 128)) => do
      v_5245 <- getRegister v_3066;
      v_5246 <- eval (extract v_5245 0 16);
      v_5253 <- eval (extract v_5245 16 32);
      v_5260 <- eval (extract v_5245 32 48);
      v_5267 <- eval (extract v_5245 48 64);
      v_5274 <- eval (extract v_5245 64 80);
      v_5281 <- eval (extract v_5245 80 96);
      v_5288 <- eval (extract v_5245 96 112);
      v_5295 <- eval (extract v_5245 112 128);
      setRegister (lhs.of_reg v_3067) (concat (mux (ugt v_5246 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5246 (mi (bitwidthMInt v_5246) -1))) v_5246) (concat (mux (ugt v_5253 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5253 (mi (bitwidthMInt v_5253) -1))) v_5253) (concat (mux (ugt v_5260 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5260 (mi (bitwidthMInt v_5260) -1))) v_5260) (concat (mux (ugt v_5267 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5267 (mi (bitwidthMInt v_5267) -1))) v_5267) (concat (mux (ugt v_5274 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5274 (mi (bitwidthMInt v_5274) -1))) v_5274) (concat (mux (ugt v_5281 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5281 (mi (bitwidthMInt v_5281) -1))) v_5281) (concat (mux (ugt v_5288 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5288 (mi (bitwidthMInt v_5288) -1))) v_5288) (mux (ugt v_5295 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5295 (mi (bitwidthMInt v_5295) -1))) v_5295))))))));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) (v_3062 : reg (bv 128)) => do
      v_9356 <- evaluateAddress v_3061;
      v_9357 <- load v_9356 16;
      v_9358 <- eval (extract v_9357 0 16);
      v_9365 <- eval (extract v_9357 16 32);
      v_9372 <- eval (extract v_9357 32 48);
      v_9379 <- eval (extract v_9357 48 64);
      v_9386 <- eval (extract v_9357 64 80);
      v_9393 <- eval (extract v_9357 80 96);
      v_9400 <- eval (extract v_9357 96 112);
      v_9407 <- eval (extract v_9357 112 128);
      setRegister (lhs.of_reg v_3062) (concat (mux (ugt v_9358 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9358 (mi (bitwidthMInt v_9358) -1))) v_9358) (concat (mux (ugt v_9365 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9365 (mi (bitwidthMInt v_9365) -1))) v_9365) (concat (mux (ugt v_9372 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9372 (mi (bitwidthMInt v_9372) -1))) v_9372) (concat (mux (ugt v_9379 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9379 (mi (bitwidthMInt v_9379) -1))) v_9379) (concat (mux (ugt v_9386 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9386 (mi (bitwidthMInt v_9386) -1))) v_9386) (concat (mux (ugt v_9393 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9393 (mi (bitwidthMInt v_9393) -1))) v_9393) (concat (mux (ugt v_9400 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9400 (mi (bitwidthMInt v_9400) -1))) v_9400) (mux (ugt v_9407 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9407 (mi (bitwidthMInt v_9407) -1))) v_9407))))))));
      pure ()
    pat_end
