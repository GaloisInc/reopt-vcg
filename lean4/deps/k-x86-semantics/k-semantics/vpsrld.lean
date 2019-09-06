def vpsrld1 : instruction :=
  definst "vpsrld" $ do
    pattern fun (v_3373 : imm int) (v_3375 : reg (bv 128)) (v_3376 : reg (bv 128)) => do
      v_8599 <- eval (handleImmediateWithSignExtend v_3373 8 8);
      v_8602 <- getRegister v_3375;
      v_8604 <- eval (concat (expression.bv_nat 24 0) v_8599);
      setRegister (lhs.of_reg v_3376) (mux (ugt (concat (expression.bv_nat 56 0) v_8599) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8602 0 32) v_8604) (concat (lshr (extract v_8602 32 64) v_8604) (concat (lshr (extract v_8602 64 96) v_8604) (lshr (extract v_8602 96 128) v_8604)))));
      pure ()
    pat_end;
    pattern fun (v_3385 : reg (bv 128)) (v_3386 : reg (bv 128)) (v_3387 : reg (bv 128)) => do
      v_8622 <- getRegister v_3385;
      v_8625 <- getRegister v_3386;
      v_8627 <- eval (extract v_8622 96 128);
      setRegister (lhs.of_reg v_3387) (mux (ugt (extract v_8622 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8625 0 32) v_8627) (concat (lshr (extract v_8625 32 64) v_8627) (concat (lshr (extract v_8625 64 96) v_8627) (lshr (extract v_8625 96 128) v_8627)))));
      pure ()
    pat_end;
    pattern fun (v_3390 : imm int) (v_3392 : reg (bv 256)) (v_3393 : reg (bv 256)) => do
      v_8640 <- eval (handleImmediateWithSignExtend v_3390 8 8);
      v_8643 <- getRegister v_3392;
      v_8645 <- eval (concat (expression.bv_nat 24 0) v_8640);
      setRegister (lhs.of_reg v_3393) (mux (ugt (concat (expression.bv_nat 56 0) v_8640) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8643 0 32) v_8645) (concat (lshr (extract v_8643 32 64) v_8645) (concat (lshr (extract v_8643 64 96) v_8645) (concat (lshr (extract v_8643 96 128) v_8645) (concat (lshr (extract v_8643 128 160) v_8645) (concat (lshr (extract v_8643 160 192) v_8645) (concat (lshr (extract v_8643 192 224) v_8645) (lshr (extract v_8643 224 256) v_8645)))))))));
      pure ()
    pat_end;
    pattern fun (v_3404 : reg (bv 128)) (v_3402 : reg (bv 256)) (v_3403 : reg (bv 256)) => do
      v_8675 <- getRegister v_3404;
      v_8678 <- getRegister v_3402;
      v_8680 <- eval (extract v_8675 96 128);
      setRegister (lhs.of_reg v_3403) (mux (ugt (extract v_8675 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8678 0 32) v_8680) (concat (lshr (extract v_8678 32 64) v_8680) (concat (lshr (extract v_8678 64 96) v_8680) (concat (lshr (extract v_8678 96 128) v_8680) (concat (lshr (extract v_8678 128 160) v_8680) (concat (lshr (extract v_8678 160 192) v_8680) (concat (lshr (extract v_8678 192 224) v_8680) (lshr (extract v_8678 224 256) v_8680)))))))));
      pure ()
    pat_end;
    pattern fun (v_3379 : Mem) (v_3380 : reg (bv 128)) (v_3381 : reg (bv 128)) => do
      v_14455 <- evaluateAddress v_3379;
      v_14456 <- load v_14455 16;
      v_14459 <- getRegister v_3380;
      v_14461 <- eval (extract v_14456 96 128);
      setRegister (lhs.of_reg v_3381) (mux (ugt (extract v_14456 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14459 0 32) v_14461) (concat (lshr (extract v_14459 32 64) v_14461) (concat (lshr (extract v_14459 64 96) v_14461) (lshr (extract v_14459 96 128) v_14461)))));
      pure ()
    pat_end;
    pattern fun (v_3396 : Mem) (v_3397 : reg (bv 256)) (v_3398 : reg (bv 256)) => do
      v_14474 <- evaluateAddress v_3396;
      v_14475 <- load v_14474 16;
      v_14478 <- getRegister v_3397;
      v_14480 <- eval (extract v_14475 96 128);
      setRegister (lhs.of_reg v_3398) (mux (ugt (extract v_14475 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_14478 0 32) v_14480) (concat (lshr (extract v_14478 32 64) v_14480) (concat (lshr (extract v_14478 64 96) v_14480) (concat (lshr (extract v_14478 96 128) v_14480) (concat (lshr (extract v_14478 128 160) v_14480) (concat (lshr (extract v_14478 160 192) v_14480) (concat (lshr (extract v_14478 192 224) v_14480) (lshr (extract v_14478 224 256) v_14480)))))))));
      pure ()
    pat_end
