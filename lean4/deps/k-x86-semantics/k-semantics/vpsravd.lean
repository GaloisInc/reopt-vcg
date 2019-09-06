def vpsravd1 : instruction :=
  definst "vpsravd" $ do
    pattern fun (v_3323 : reg (bv 128)) (v_3324 : reg (bv 128)) (v_3325 : reg (bv 128)) => do
      v_8364 <- getRegister v_3324;
      v_8366 <- getRegister v_3323;
      setRegister (lhs.of_reg v_3325) (concat (ashr (extract v_8364 0 32) (extract v_8366 0 32)) (concat (ashr (extract v_8364 32 64) (extract v_8366 32 64)) (concat (ashr (extract v_8364 64 96) (extract v_8366 64 96)) (ashr (extract v_8364 96 128) (extract v_8366 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3334 : reg (bv 256)) (v_3335 : reg (bv 256)) (v_3336 : reg (bv 256)) => do
      v_8387 <- getRegister v_3335;
      v_8389 <- getRegister v_3334;
      setRegister (lhs.of_reg v_3336) (concat (ashr (extract v_8387 0 32) (extract v_8389 0 32)) (concat (ashr (extract v_8387 32 64) (extract v_8389 32 64)) (concat (ashr (extract v_8387 64 96) (extract v_8389 64 96)) (concat (ashr (extract v_8387 96 128) (extract v_8389 96 128)) (concat (ashr (extract v_8387 128 160) (extract v_8389 128 160)) (concat (ashr (extract v_8387 160 192) (extract v_8389 160 192)) (concat (ashr (extract v_8387 192 224) (extract v_8389 192 224)) (ashr (extract v_8387 224 256) (extract v_8389 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3318 : reg (bv 128)) (v_3319 : reg (bv 128)) => do
      v_14315 <- getRegister v_3318;
      v_14317 <- evaluateAddress v_3317;
      v_14318 <- load v_14317 16;
      setRegister (lhs.of_reg v_3319) (concat (ashr (extract v_14315 0 32) (extract v_14318 0 32)) (concat (ashr (extract v_14315 32 64) (extract v_14318 32 64)) (concat (ashr (extract v_14315 64 96) (extract v_14318 64 96)) (ashr (extract v_14315 96 128) (extract v_14318 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3328 : Mem) (v_3329 : reg (bv 256)) (v_3330 : reg (bv 256)) => do
      v_14334 <- getRegister v_3329;
      v_14336 <- evaluateAddress v_3328;
      v_14337 <- load v_14336 32;
      setRegister (lhs.of_reg v_3330) (concat (ashr (extract v_14334 0 32) (extract v_14337 0 32)) (concat (ashr (extract v_14334 32 64) (extract v_14337 32 64)) (concat (ashr (extract v_14334 64 96) (extract v_14337 64 96)) (concat (ashr (extract v_14334 96 128) (extract v_14337 96 128)) (concat (ashr (extract v_14334 128 160) (extract v_14337 128 160)) (concat (ashr (extract v_14334 160 192) (extract v_14337 160 192)) (concat (ashr (extract v_14334 192 224) (extract v_14337 192 224)) (ashr (extract v_14334 224 256) (extract v_14337 224 256)))))))));
      pure ()
    pat_end
