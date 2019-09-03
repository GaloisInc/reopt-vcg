def pabsw1 : instruction :=
  definst "pabsw" $ do
    pattern fun (v_3078 : reg (bv 128)) (v_3079 : reg (bv 128)) => do
      v_5292 <- getRegister v_3078;
      v_5293 <- eval (extract v_5292 0 16);
      v_5298 <- eval (extract v_5292 16 32);
      v_5303 <- eval (extract v_5292 32 48);
      v_5308 <- eval (extract v_5292 48 64);
      v_5313 <- eval (extract v_5292 64 80);
      v_5318 <- eval (extract v_5292 80 96);
      v_5323 <- eval (extract v_5292 96 112);
      v_5328 <- eval (extract v_5292 112 128);
      setRegister (lhs.of_reg v_3079) (concat (mux (ugt v_5293 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5293 (expression.bv_nat 16 65535))) v_5293) (concat (mux (ugt v_5298 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5298 (expression.bv_nat 16 65535))) v_5298) (concat (mux (ugt v_5303 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5303 (expression.bv_nat 16 65535))) v_5303) (concat (mux (ugt v_5308 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5308 (expression.bv_nat 16 65535))) v_5308) (concat (mux (ugt v_5313 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5313 (expression.bv_nat 16 65535))) v_5313) (concat (mux (ugt v_5318 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5318 (expression.bv_nat 16 65535))) v_5318) (concat (mux (ugt v_5323 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5323 (expression.bv_nat 16 65535))) v_5323) (mux (ugt v_5328 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5328 (expression.bv_nat 16 65535))) v_5328))))))));
      pure ()
    pat_end;
    pattern fun (v_3074 : Mem) (v_3075 : reg (bv 128)) => do
      v_9391 <- evaluateAddress v_3074;
      v_9392 <- load v_9391 16;
      v_9393 <- eval (extract v_9392 0 16);
      v_9398 <- eval (extract v_9392 16 32);
      v_9403 <- eval (extract v_9392 32 48);
      v_9408 <- eval (extract v_9392 48 64);
      v_9413 <- eval (extract v_9392 64 80);
      v_9418 <- eval (extract v_9392 80 96);
      v_9423 <- eval (extract v_9392 96 112);
      v_9428 <- eval (extract v_9392 112 128);
      setRegister (lhs.of_reg v_3075) (concat (mux (ugt v_9393 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9393 (expression.bv_nat 16 65535))) v_9393) (concat (mux (ugt v_9398 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9398 (expression.bv_nat 16 65535))) v_9398) (concat (mux (ugt v_9403 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9403 (expression.bv_nat 16 65535))) v_9403) (concat (mux (ugt v_9408 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9408 (expression.bv_nat 16 65535))) v_9408) (concat (mux (ugt v_9413 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9413 (expression.bv_nat 16 65535))) v_9413) (concat (mux (ugt v_9418 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9418 (expression.bv_nat 16 65535))) v_9418) (concat (mux (ugt v_9423 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9423 (expression.bv_nat 16 65535))) v_9423) (mux (ugt v_9428 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9428 (expression.bv_nat 16 65535))) v_9428))))))));
      pure ()
    pat_end
