def vpsrlq1 : instruction :=
  definst "vpsrlq" $ do
    pattern fun (v_3330 : imm int) (v_3328 : reg (bv 128)) (v_3329 : reg (bv 128)) => do
      v_9358 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3330 8 8));
      v_9360 <- getRegister v_3328;
      v_9362 <- eval (uvalueMInt v_9358);
      setRegister (lhs.of_reg v_3329) (mux (ugt v_9358 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_9360 0 64) v_9362) (lshr (extract v_9360 64 128) v_9362)));
      pure ()
    pat_end;
    pattern fun (v_3339 : reg (bv 128)) (v_3340 : reg (bv 128)) (v_3341 : reg (bv 128)) => do
      v_9374 <- getRegister v_3339;
      v_9375 <- eval (extract v_9374 64 128);
      v_9377 <- getRegister v_3340;
      v_9379 <- eval (uvalueMInt v_9375);
      setRegister (lhs.of_reg v_3341) (mux (ugt v_9375 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_9377 0 64) v_9379) (lshr (extract v_9377 64 128) v_9379)));
      pure ()
    pat_end;
    pattern fun (v_3345 : imm int) (v_3346 : reg (bv 256)) (v_3347 : reg (bv 256)) => do
      v_9387 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3345 8 8));
      v_9389 <- getRegister v_3346;
      v_9391 <- eval (uvalueMInt v_9387);
      setRegister (lhs.of_reg v_3347) (mux (ugt v_9387 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_9389 0 64) v_9391) (concat (lshr (extract v_9389 64 128) v_9391) (concat (lshr (extract v_9389 128 192) v_9391) (lshr (extract v_9389 192 256) v_9391)))));
      pure ()
    pat_end;
    pattern fun (v_3356 : reg (bv 128)) (v_3357 : reg (bv 256)) (v_3358 : reg (bv 256)) => do
      v_9409 <- getRegister v_3356;
      v_9410 <- eval (extract v_9409 64 128);
      v_9412 <- getRegister v_3357;
      v_9414 <- eval (uvalueMInt v_9410);
      setRegister (lhs.of_reg v_3358) (mux (ugt v_9410 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_9412 0 64) v_9414) (concat (lshr (extract v_9412 64 128) v_9414) (concat (lshr (extract v_9412 128 192) v_9414) (lshr (extract v_9412 192 256) v_9414)))));
      pure ()
    pat_end;
    pattern fun (v_3336 : Mem) (v_3334 : reg (bv 128)) (v_3335 : reg (bv 128)) => do
      v_15709 <- evaluateAddress v_3336;
      v_15710 <- load v_15709 16;
      v_15711 <- eval (extract v_15710 64 128);
      v_15713 <- getRegister v_3334;
      v_15715 <- eval (uvalueMInt v_15711);
      setRegister (lhs.of_reg v_3335) (mux (ugt v_15711 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_15713 0 64) v_15715) (lshr (extract v_15713 64 128) v_15715)));
      pure ()
    pat_end;
    pattern fun (v_3351 : Mem) (v_3352 : reg (bv 256)) (v_3353 : reg (bv 256)) => do
      v_15722 <- evaluateAddress v_3351;
      v_15723 <- load v_15722 16;
      v_15724 <- eval (extract v_15723 64 128);
      v_15726 <- getRegister v_3352;
      v_15728 <- eval (uvalueMInt v_15724);
      setRegister (lhs.of_reg v_3353) (mux (ugt v_15724 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_15726 0 64) v_15728) (concat (lshr (extract v_15726 64 128) v_15728) (concat (lshr (extract v_15726 128 192) v_15728) (lshr (extract v_15726 192 256) v_15728)))));
      pure ()
    pat_end
