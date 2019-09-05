def vpsrad1 : instruction :=
  definst "vpsrad" $ do
    pattern fun (v_3254 : imm int) (v_3258 : reg (bv 128)) (v_3259 : reg (bv 128)) => do
      v_8226 <- getRegister v_3258;
      v_8228 <- eval (handleImmediateWithSignExtend v_3254 8 8);
      v_8232 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8228) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8228));
      setRegister (lhs.of_reg v_3259) (concat (ashr (extract v_8226 0 32) v_8232) (concat (ashr (extract v_8226 32 64) v_8232) (concat (ashr (extract v_8226 64 96) v_8232) (ashr (extract v_8226 96 128) v_8232))));
      pure ()
    pat_end;
    pattern fun (v_3268 : reg (bv 128)) (v_3269 : reg (bv 128)) (v_3270 : reg (bv 128)) => do
      v_8249 <- getRegister v_3269;
      v_8251 <- getRegister v_3268;
      v_8255 <- eval (mux (ugt (extract v_8251 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8251 96 128));
      setRegister (lhs.of_reg v_3270) (concat (ashr (extract v_8249 0 32) v_8255) (concat (ashr (extract v_8249 32 64) v_8255) (concat (ashr (extract v_8249 64 96) v_8255) (ashr (extract v_8249 96 128) v_8255))));
      pure ()
    pat_end;
    pattern fun (v_3271 : imm int) (v_3275 : reg (bv 256)) (v_3276 : reg (bv 256)) => do
      v_8267 <- getRegister v_3275;
      v_8269 <- eval (handleImmediateWithSignExtend v_3271 8 8);
      v_8273 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8269) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8269));
      setRegister (lhs.of_reg v_3276) (concat (ashr (extract v_8267 0 32) v_8273) (concat (ashr (extract v_8267 32 64) v_8273) (concat (ashr (extract v_8267 64 96) v_8273) (concat (ashr (extract v_8267 96 128) v_8273) (concat (ashr (extract v_8267 128 160) v_8273) (concat (ashr (extract v_8267 160 192) v_8273) (concat (ashr (extract v_8267 192 224) v_8273) (ashr (extract v_8267 224 256) v_8273))))))));
      pure ()
    pat_end;
    pattern fun (v_3287 : reg (bv 128)) (v_3285 : reg (bv 256)) (v_3286 : reg (bv 256)) => do
      v_8302 <- getRegister v_3285;
      v_8304 <- getRegister v_3287;
      v_8308 <- eval (mux (ugt (extract v_8304 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8304 96 128));
      setRegister (lhs.of_reg v_3286) (concat (ashr (extract v_8302 0 32) v_8308) (concat (ashr (extract v_8302 32 64) v_8308) (concat (ashr (extract v_8302 64 96) v_8308) (concat (ashr (extract v_8302 96 128) v_8308) (concat (ashr (extract v_8302 128 160) v_8308) (concat (ashr (extract v_8302 160 192) v_8308) (concat (ashr (extract v_8302 192 224) v_8308) (ashr (extract v_8302 224 256) v_8308))))))));
      pure ()
    pat_end;
    pattern fun (v_3262 : Mem) (v_3263 : reg (bv 128)) (v_3264 : reg (bv 128)) => do
      v_14238 <- getRegister v_3263;
      v_14240 <- evaluateAddress v_3262;
      v_14241 <- load v_14240 16;
      v_14245 <- eval (mux (ugt (extract v_14241 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14241 96 128));
      setRegister (lhs.of_reg v_3264) (concat (ashr (extract v_14238 0 32) v_14245) (concat (ashr (extract v_14238 32 64) v_14245) (concat (ashr (extract v_14238 64 96) v_14245) (ashr (extract v_14238 96 128) v_14245))));
      pure ()
    pat_end;
    pattern fun (v_3279 : Mem) (v_3280 : reg (bv 256)) (v_3281 : reg (bv 256)) => do
      v_14257 <- getRegister v_3280;
      v_14259 <- evaluateAddress v_3279;
      v_14260 <- load v_14259 16;
      v_14264 <- eval (mux (ugt (extract v_14260 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14260 96 128));
      setRegister (lhs.of_reg v_3281) (concat (ashr (extract v_14257 0 32) v_14264) (concat (ashr (extract v_14257 32 64) v_14264) (concat (ashr (extract v_14257 64 96) v_14264) (concat (ashr (extract v_14257 96 128) v_14264) (concat (ashr (extract v_14257 128 160) v_14264) (concat (ashr (extract v_14257 160 192) v_14264) (concat (ashr (extract v_14257 192 224) v_14264) (ashr (extract v_14257 224 256) v_14264))))))));
      pure ()
    pat_end
