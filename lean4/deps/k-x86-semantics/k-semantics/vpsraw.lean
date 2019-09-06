def vpsraw1 : instruction :=
  definst "vpsraw" $ do
    pattern fun (v_3339 : imm int) (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) => do
      v_8421 <- getRegister v_3341;
      v_8423 <- eval (handleImmediateWithSignExtend v_3339 8 8);
      v_8427 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8423) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8423));
      setRegister (lhs.of_reg v_3342) (concat (ashr (extract v_8421 0 16) v_8427) (concat (ashr (extract v_8421 16 32) v_8427) (concat (ashr (extract v_8421 32 48) v_8427) (concat (ashr (extract v_8421 48 64) v_8427) (concat (ashr (extract v_8421 64 80) v_8427) (concat (ashr (extract v_8421 80 96) v_8427) (concat (ashr (extract v_8421 96 112) v_8427) (ashr (extract v_8421 112 128) v_8427))))))));
      pure ()
    pat_end;
    pattern fun (v_3351 : reg (bv 128)) (v_3352 : reg (bv 128)) (v_3353 : reg (bv 128)) => do
      v_8456 <- getRegister v_3352;
      v_8458 <- getRegister v_3351;
      v_8462 <- eval (mux (ugt (extract v_8458 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8458 112 128));
      setRegister (lhs.of_reg v_3353) (concat (ashr (extract v_8456 0 16) v_8462) (concat (ashr (extract v_8456 16 32) v_8462) (concat (ashr (extract v_8456 32 48) v_8462) (concat (ashr (extract v_8456 48 64) v_8462) (concat (ashr (extract v_8456 64 80) v_8462) (concat (ashr (extract v_8456 80 96) v_8462) (concat (ashr (extract v_8456 96 112) v_8462) (ashr (extract v_8456 112 128) v_8462))))))));
      pure ()
    pat_end;
    pattern fun (v_3356 : imm int) (v_3358 : reg (bv 256)) (v_3359 : reg (bv 256)) => do
      v_8486 <- getRegister v_3358;
      v_8488 <- eval (handleImmediateWithSignExtend v_3356 8 8);
      v_8492 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8488) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8488));
      setRegister (lhs.of_reg v_3359) (concat (ashr (extract v_8486 0 16) v_8492) (concat (ashr (extract v_8486 16 32) v_8492) (concat (ashr (extract v_8486 32 48) v_8492) (concat (ashr (extract v_8486 48 64) v_8492) (concat (ashr (extract v_8486 64 80) v_8492) (concat (ashr (extract v_8486 80 96) v_8492) (concat (ashr (extract v_8486 96 112) v_8492) (concat (ashr (extract v_8486 112 128) v_8492) (concat (ashr (extract v_8486 128 144) v_8492) (concat (ashr (extract v_8486 144 160) v_8492) (concat (ashr (extract v_8486 160 176) v_8492) (concat (ashr (extract v_8486 176 192) v_8492) (concat (ashr (extract v_8486 192 208) v_8492) (concat (ashr (extract v_8486 208 224) v_8492) (concat (ashr (extract v_8486 224 240) v_8492) (ashr (extract v_8486 240 256) v_8492))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3370 : reg (bv 128)) (v_3368 : reg (bv 256)) (v_3369 : reg (bv 256)) => do
      v_8545 <- getRegister v_3368;
      v_8547 <- getRegister v_3370;
      v_8551 <- eval (mux (ugt (extract v_8547 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8547 112 128));
      setRegister (lhs.of_reg v_3369) (concat (ashr (extract v_8545 0 16) v_8551) (concat (ashr (extract v_8545 16 32) v_8551) (concat (ashr (extract v_8545 32 48) v_8551) (concat (ashr (extract v_8545 48 64) v_8551) (concat (ashr (extract v_8545 64 80) v_8551) (concat (ashr (extract v_8545 80 96) v_8551) (concat (ashr (extract v_8545 96 112) v_8551) (concat (ashr (extract v_8545 112 128) v_8551) (concat (ashr (extract v_8545 128 144) v_8551) (concat (ashr (extract v_8545 144 160) v_8551) (concat (ashr (extract v_8545 160 176) v_8551) (concat (ashr (extract v_8545 176 192) v_8551) (concat (ashr (extract v_8545 192 208) v_8551) (concat (ashr (extract v_8545 208 224) v_8551) (concat (ashr (extract v_8545 224 240) v_8551) (ashr (extract v_8545 240 256) v_8551))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3345 : Mem) (v_3346 : reg (bv 128)) (v_3347 : reg (bv 128)) => do
      v_14369 <- getRegister v_3346;
      v_14371 <- evaluateAddress v_3345;
      v_14372 <- load v_14371 16;
      v_14376 <- eval (mux (ugt (extract v_14372 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14372 112 128));
      setRegister (lhs.of_reg v_3347) (concat (ashr (extract v_14369 0 16) v_14376) (concat (ashr (extract v_14369 16 32) v_14376) (concat (ashr (extract v_14369 32 48) v_14376) (concat (ashr (extract v_14369 48 64) v_14376) (concat (ashr (extract v_14369 64 80) v_14376) (concat (ashr (extract v_14369 80 96) v_14376) (concat (ashr (extract v_14369 96 112) v_14376) (ashr (extract v_14369 112 128) v_14376))))))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3363 : reg (bv 256)) (v_3364 : reg (bv 256)) => do
      v_14400 <- getRegister v_3363;
      v_14402 <- evaluateAddress v_3362;
      v_14403 <- load v_14402 16;
      v_14407 <- eval (mux (ugt (extract v_14403 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14403 112 128));
      setRegister (lhs.of_reg v_3364) (concat (ashr (extract v_14400 0 16) v_14407) (concat (ashr (extract v_14400 16 32) v_14407) (concat (ashr (extract v_14400 32 48) v_14407) (concat (ashr (extract v_14400 48 64) v_14407) (concat (ashr (extract v_14400 64 80) v_14407) (concat (ashr (extract v_14400 80 96) v_14407) (concat (ashr (extract v_14400 96 112) v_14407) (concat (ashr (extract v_14400 112 128) v_14407) (concat (ashr (extract v_14400 128 144) v_14407) (concat (ashr (extract v_14400 144 160) v_14407) (concat (ashr (extract v_14400 160 176) v_14407) (concat (ashr (extract v_14400 176 192) v_14407) (concat (ashr (extract v_14400 192 208) v_14407) (concat (ashr (extract v_14400 208 224) v_14407) (concat (ashr (extract v_14400 224 240) v_14407) (ashr (extract v_14400 240 256) v_14407))))))))))))))));
      pure ()
    pat_end
