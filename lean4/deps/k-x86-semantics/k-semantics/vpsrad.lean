def vpsrad1 : instruction :=
  definst "vpsrad" $ do
    pattern fun (v_3283 : imm int) (v_3285 : reg (bv 128)) (v_3286 : reg (bv 128)) => do
      v_8253 <- getRegister v_3285;
      v_8255 <- eval (handleImmediateWithSignExtend v_3283 8 8);
      v_8259 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8255) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8255));
      setRegister (lhs.of_reg v_3286) (concat (ashr (extract v_8253 0 32) v_8259) (concat (ashr (extract v_8253 32 64) v_8259) (concat (ashr (extract v_8253 64 96) v_8259) (ashr (extract v_8253 96 128) v_8259))));
      pure ()
    pat_end;
    pattern fun (v_3295 : reg (bv 128)) (v_3296 : reg (bv 128)) (v_3297 : reg (bv 128)) => do
      v_8276 <- getRegister v_3296;
      v_8278 <- getRegister v_3295;
      v_8282 <- eval (mux (ugt (extract v_8278 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8278 96 128));
      setRegister (lhs.of_reg v_3297) (concat (ashr (extract v_8276 0 32) v_8282) (concat (ashr (extract v_8276 32 64) v_8282) (concat (ashr (extract v_8276 64 96) v_8282) (ashr (extract v_8276 96 128) v_8282))));
      pure ()
    pat_end;
    pattern fun (v_3300 : imm int) (v_3302 : reg (bv 256)) (v_3303 : reg (bv 256)) => do
      v_8294 <- getRegister v_3302;
      v_8296 <- eval (handleImmediateWithSignExtend v_3300 8 8);
      v_8300 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_8296) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8296));
      setRegister (lhs.of_reg v_3303) (concat (ashr (extract v_8294 0 32) v_8300) (concat (ashr (extract v_8294 32 64) v_8300) (concat (ashr (extract v_8294 64 96) v_8300) (concat (ashr (extract v_8294 96 128) v_8300) (concat (ashr (extract v_8294 128 160) v_8300) (concat (ashr (extract v_8294 160 192) v_8300) (concat (ashr (extract v_8294 192 224) v_8300) (ashr (extract v_8294 224 256) v_8300))))))));
      pure ()
    pat_end;
    pattern fun (v_3314 : reg (bv 128)) (v_3312 : reg (bv 256)) (v_3313 : reg (bv 256)) => do
      v_8329 <- getRegister v_3312;
      v_8331 <- getRegister v_3314;
      v_8335 <- eval (mux (ugt (extract v_8331 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8331 96 128));
      setRegister (lhs.of_reg v_3313) (concat (ashr (extract v_8329 0 32) v_8335) (concat (ashr (extract v_8329 32 64) v_8335) (concat (ashr (extract v_8329 64 96) v_8335) (concat (ashr (extract v_8329 96 128) v_8335) (concat (ashr (extract v_8329 128 160) v_8335) (concat (ashr (extract v_8329 160 192) v_8335) (concat (ashr (extract v_8329 192 224) v_8335) (ashr (extract v_8329 224 256) v_8335))))))));
      pure ()
    pat_end;
    pattern fun (v_3289 : Mem) (v_3290 : reg (bv 128)) (v_3291 : reg (bv 128)) => do
      v_14265 <- getRegister v_3290;
      v_14267 <- evaluateAddress v_3289;
      v_14268 <- load v_14267 16;
      v_14272 <- eval (mux (ugt (extract v_14268 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14268 96 128));
      setRegister (lhs.of_reg v_3291) (concat (ashr (extract v_14265 0 32) v_14272) (concat (ashr (extract v_14265 32 64) v_14272) (concat (ashr (extract v_14265 64 96) v_14272) (ashr (extract v_14265 96 128) v_14272))));
      pure ()
    pat_end;
    pattern fun (v_3306 : Mem) (v_3307 : reg (bv 256)) (v_3308 : reg (bv 256)) => do
      v_14284 <- getRegister v_3307;
      v_14286 <- evaluateAddress v_3306;
      v_14287 <- load v_14286 16;
      v_14291 <- eval (mux (ugt (extract v_14287 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14287 96 128));
      setRegister (lhs.of_reg v_3308) (concat (ashr (extract v_14284 0 32) v_14291) (concat (ashr (extract v_14284 32 64) v_14291) (concat (ashr (extract v_14284 64 96) v_14291) (concat (ashr (extract v_14284 96 128) v_14291) (concat (ashr (extract v_14284 128 160) v_14291) (concat (ashr (extract v_14284 160 192) v_14291) (concat (ashr (extract v_14284 192 224) v_14291) (ashr (extract v_14284 224 256) v_14291))))))));
      pure ()
    pat_end
