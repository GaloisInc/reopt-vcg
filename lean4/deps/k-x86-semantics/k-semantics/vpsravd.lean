def vpsravd1 : instruction :=
  definst "vpsravd" $ do
    pattern fun (v_3296 : reg (bv 128)) (v_3297 : reg (bv 128)) (v_3298 : reg (bv 128)) => do
      v_8337 <- getRegister v_3297;
      v_8339 <- getRegister v_3296;
      setRegister (lhs.of_reg v_3298) (concat (ashr (extract v_8337 0 32) (extract v_8339 0 32)) (concat (ashr (extract v_8337 32 64) (extract v_8339 32 64)) (concat (ashr (extract v_8337 64 96) (extract v_8339 64 96)) (ashr (extract v_8337 96 128) (extract v_8339 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3307 : reg (bv 256)) (v_3308 : reg (bv 256)) (v_3309 : reg (bv 256)) => do
      v_8360 <- getRegister v_3308;
      v_8362 <- getRegister v_3307;
      setRegister (lhs.of_reg v_3309) (concat (ashr (extract v_8360 0 32) (extract v_8362 0 32)) (concat (ashr (extract v_8360 32 64) (extract v_8362 32 64)) (concat (ashr (extract v_8360 64 96) (extract v_8362 64 96)) (concat (ashr (extract v_8360 96 128) (extract v_8362 96 128)) (concat (ashr (extract v_8360 128 160) (extract v_8362 128 160)) (concat (ashr (extract v_8360 160 192) (extract v_8362 160 192)) (concat (ashr (extract v_8360 192 224) (extract v_8362 192 224)) (ashr (extract v_8360 224 256) (extract v_8362 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3290 : Mem) (v_3291 : reg (bv 128)) (v_3292 : reg (bv 128)) => do
      v_14288 <- getRegister v_3291;
      v_14290 <- evaluateAddress v_3290;
      v_14291 <- load v_14290 16;
      setRegister (lhs.of_reg v_3292) (concat (ashr (extract v_14288 0 32) (extract v_14291 0 32)) (concat (ashr (extract v_14288 32 64) (extract v_14291 32 64)) (concat (ashr (extract v_14288 64 96) (extract v_14291 64 96)) (ashr (extract v_14288 96 128) (extract v_14291 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3301 : Mem) (v_3302 : reg (bv 256)) (v_3303 : reg (bv 256)) => do
      v_14307 <- getRegister v_3302;
      v_14309 <- evaluateAddress v_3301;
      v_14310 <- load v_14309 32;
      setRegister (lhs.of_reg v_3303) (concat (ashr (extract v_14307 0 32) (extract v_14310 0 32)) (concat (ashr (extract v_14307 32 64) (extract v_14310 32 64)) (concat (ashr (extract v_14307 64 96) (extract v_14310 64 96)) (concat (ashr (extract v_14307 96 128) (extract v_14310 96 128)) (concat (ashr (extract v_14307 128 160) (extract v_14310 128 160)) (concat (ashr (extract v_14307 160 192) (extract v_14310 160 192)) (concat (ashr (extract v_14307 192 224) (extract v_14310 192 224)) (ashr (extract v_14307 224 256) (extract v_14310 224 256)))))))));
      pure ()
    pat_end
