def vpsraw1 : instruction :=
  definst "vpsraw" $ do
    pattern fun (v_3310 : imm int) (v_3314 : reg (bv 128)) (v_3315 : reg (bv 128)) => do
      v_8394 <- getRegister v_3314;
      v_8396 <- eval (handleImmediateWithSignExtend v_3310 8 8);
      v_8400 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8396) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8396));
      setRegister (lhs.of_reg v_3315) (concat (ashr (extract v_8394 0 16) v_8400) (concat (ashr (extract v_8394 16 32) v_8400) (concat (ashr (extract v_8394 32 48) v_8400) (concat (ashr (extract v_8394 48 64) v_8400) (concat (ashr (extract v_8394 64 80) v_8400) (concat (ashr (extract v_8394 80 96) v_8400) (concat (ashr (extract v_8394 96 112) v_8400) (ashr (extract v_8394 112 128) v_8400))))))));
      pure ()
    pat_end;
    pattern fun (v_3324 : reg (bv 128)) (v_3325 : reg (bv 128)) (v_3326 : reg (bv 128)) => do
      v_8429 <- getRegister v_3325;
      v_8431 <- getRegister v_3324;
      v_8435 <- eval (mux (ugt (extract v_8431 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8431 112 128));
      setRegister (lhs.of_reg v_3326) (concat (ashr (extract v_8429 0 16) v_8435) (concat (ashr (extract v_8429 16 32) v_8435) (concat (ashr (extract v_8429 32 48) v_8435) (concat (ashr (extract v_8429 48 64) v_8435) (concat (ashr (extract v_8429 64 80) v_8435) (concat (ashr (extract v_8429 80 96) v_8435) (concat (ashr (extract v_8429 96 112) v_8435) (ashr (extract v_8429 112 128) v_8435))))))));
      pure ()
    pat_end;
    pattern fun (v_3327 : imm int) (v_3331 : reg (bv 256)) (v_3332 : reg (bv 256)) => do
      v_8459 <- getRegister v_3331;
      v_8461 <- eval (handleImmediateWithSignExtend v_3327 8 8);
      v_8465 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8461) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8461));
      setRegister (lhs.of_reg v_3332) (concat (ashr (extract v_8459 0 16) v_8465) (concat (ashr (extract v_8459 16 32) v_8465) (concat (ashr (extract v_8459 32 48) v_8465) (concat (ashr (extract v_8459 48 64) v_8465) (concat (ashr (extract v_8459 64 80) v_8465) (concat (ashr (extract v_8459 80 96) v_8465) (concat (ashr (extract v_8459 96 112) v_8465) (concat (ashr (extract v_8459 112 128) v_8465) (concat (ashr (extract v_8459 128 144) v_8465) (concat (ashr (extract v_8459 144 160) v_8465) (concat (ashr (extract v_8459 160 176) v_8465) (concat (ashr (extract v_8459 176 192) v_8465) (concat (ashr (extract v_8459 192 208) v_8465) (concat (ashr (extract v_8459 208 224) v_8465) (concat (ashr (extract v_8459 224 240) v_8465) (ashr (extract v_8459 240 256) v_8465))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3343 : reg (bv 128)) (v_3341 : reg (bv 256)) (v_3342 : reg (bv 256)) => do
      v_8518 <- getRegister v_3341;
      v_8520 <- getRegister v_3343;
      v_8524 <- eval (mux (ugt (extract v_8520 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8520 112 128));
      setRegister (lhs.of_reg v_3342) (concat (ashr (extract v_8518 0 16) v_8524) (concat (ashr (extract v_8518 16 32) v_8524) (concat (ashr (extract v_8518 32 48) v_8524) (concat (ashr (extract v_8518 48 64) v_8524) (concat (ashr (extract v_8518 64 80) v_8524) (concat (ashr (extract v_8518 80 96) v_8524) (concat (ashr (extract v_8518 96 112) v_8524) (concat (ashr (extract v_8518 112 128) v_8524) (concat (ashr (extract v_8518 128 144) v_8524) (concat (ashr (extract v_8518 144 160) v_8524) (concat (ashr (extract v_8518 160 176) v_8524) (concat (ashr (extract v_8518 176 192) v_8524) (concat (ashr (extract v_8518 192 208) v_8524) (concat (ashr (extract v_8518 208 224) v_8524) (concat (ashr (extract v_8518 224 240) v_8524) (ashr (extract v_8518 240 256) v_8524))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3318 : Mem) (v_3319 : reg (bv 128)) (v_3320 : reg (bv 128)) => do
      v_14342 <- getRegister v_3319;
      v_14344 <- evaluateAddress v_3318;
      v_14345 <- load v_14344 16;
      v_14349 <- eval (mux (ugt (extract v_14345 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14345 112 128));
      setRegister (lhs.of_reg v_3320) (concat (ashr (extract v_14342 0 16) v_14349) (concat (ashr (extract v_14342 16 32) v_14349) (concat (ashr (extract v_14342 32 48) v_14349) (concat (ashr (extract v_14342 48 64) v_14349) (concat (ashr (extract v_14342 64 80) v_14349) (concat (ashr (extract v_14342 80 96) v_14349) (concat (ashr (extract v_14342 96 112) v_14349) (ashr (extract v_14342 112 128) v_14349))))))));
      pure ()
    pat_end;
    pattern fun (v_3335 : Mem) (v_3336 : reg (bv 256)) (v_3337 : reg (bv 256)) => do
      v_14373 <- getRegister v_3336;
      v_14375 <- evaluateAddress v_3335;
      v_14376 <- load v_14375 16;
      v_14380 <- eval (mux (ugt (extract v_14376 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14376 112 128));
      setRegister (lhs.of_reg v_3337) (concat (ashr (extract v_14373 0 16) v_14380) (concat (ashr (extract v_14373 16 32) v_14380) (concat (ashr (extract v_14373 32 48) v_14380) (concat (ashr (extract v_14373 48 64) v_14380) (concat (ashr (extract v_14373 64 80) v_14380) (concat (ashr (extract v_14373 80 96) v_14380) (concat (ashr (extract v_14373 96 112) v_14380) (concat (ashr (extract v_14373 112 128) v_14380) (concat (ashr (extract v_14373 128 144) v_14380) (concat (ashr (extract v_14373 144 160) v_14380) (concat (ashr (extract v_14373 160 176) v_14380) (concat (ashr (extract v_14373 176 192) v_14380) (concat (ashr (extract v_14373 192 208) v_14380) (concat (ashr (extract v_14373 208 224) v_14380) (concat (ashr (extract v_14373 224 240) v_14380) (ashr (extract v_14373 240 256) v_14380))))))))))))))));
      pure ()
    pat_end
