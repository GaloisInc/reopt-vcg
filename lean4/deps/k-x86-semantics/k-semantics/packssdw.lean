def packssdw1 : instruction :=
  definst "packssdw" $ do
    pattern fun (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_5314 <- getRegister v_3075;
      v_5315 <- eval (extract v_5314 0 32);
      v_5321 <- eval (extract v_5314 32 64);
      v_5327 <- eval (extract v_5314 64 96);
      v_5333 <- eval (extract v_5314 96 128);
      v_5339 <- getRegister v_3076;
      v_5340 <- eval (extract v_5339 0 32);
      v_5346 <- eval (extract v_5339 32 64);
      v_5352 <- eval (extract v_5339 64 96);
      v_5358 <- eval (extract v_5339 96 128);
      setRegister (lhs.of_reg v_3076) (concat (mux (sgt v_5315 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5315 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5314 16 32))) (concat (mux (sgt v_5321 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5321 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5314 48 64))) (concat (mux (sgt v_5327 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5327 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5314 80 96))) (concat (mux (sgt v_5333 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5333 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5314 112 128))) (concat (mux (sgt v_5340 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5340 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5339 16 32))) (concat (mux (sgt v_5346 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5346 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5339 48 64))) (concat (mux (sgt v_5352 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5352 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5339 80 96))) (mux (sgt v_5358 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5358 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5339 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3070 : Mem) (v_3071 : reg (bv 128)) => do
      v_9422 <- evaluateAddress v_3070;
      v_9423 <- load v_9422 16;
      v_9424 <- eval (extract v_9423 0 32);
      v_9430 <- eval (extract v_9423 32 64);
      v_9436 <- eval (extract v_9423 64 96);
      v_9442 <- eval (extract v_9423 96 128);
      v_9448 <- getRegister v_3071;
      v_9449 <- eval (extract v_9448 0 32);
      v_9455 <- eval (extract v_9448 32 64);
      v_9461 <- eval (extract v_9448 64 96);
      v_9467 <- eval (extract v_9448 96 128);
      setRegister (lhs.of_reg v_3071) (concat (mux (sgt v_9424 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9424 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9423 16 32))) (concat (mux (sgt v_9430 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9430 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9423 48 64))) (concat (mux (sgt v_9436 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9436 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9423 80 96))) (concat (mux (sgt v_9442 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9442 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9423 112 128))) (concat (mux (sgt v_9449 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9449 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9448 16 32))) (concat (mux (sgt v_9455 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9455 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9448 48 64))) (concat (mux (sgt v_9461 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9461 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9448 80 96))) (mux (sgt v_9467 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9467 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9448 112 128))))))))));
      pure ()
    pat_end
