def vpsrlq1 : instruction :=
  definst "vpsrlq" $ do
    pattern fun (v_3390 : imm int) (v_3394 : reg (bv 128)) (v_3395 : reg (bv 128)) => do
      v_8701 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3390 8 8));
      v_8703 <- getRegister v_3394;
      setRegister (lhs.of_reg v_3395) (mux (ugt v_8701 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8703 0 64) v_8701) (lshr (extract v_8703 64 128) v_8701)));
      pure ()
    pat_end;
    pattern fun (v_3404 : reg (bv 128)) (v_3405 : reg (bv 128)) (v_3406 : reg (bv 128)) => do
      v_8716 <- getRegister v_3404;
      v_8717 <- eval (extract v_8716 64 128);
      v_8719 <- getRegister v_3405;
      setRegister (lhs.of_reg v_3406) (mux (ugt v_8717 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8719 0 64) v_8717) (lshr (extract v_8719 64 128) v_8717)));
      pure ()
    pat_end;
    pattern fun (v_3407 : imm int) (v_3411 : reg (bv 256)) (v_3412 : reg (bv 256)) => do
      v_8728 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3407 8 8));
      v_8730 <- getRegister v_3411;
      setRegister (lhs.of_reg v_3412) (mux (ugt v_8728 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8730 0 64) v_8728) (concat (lshr (extract v_8730 64 128) v_8728) (concat (lshr (extract v_8730 128 192) v_8728) (lshr (extract v_8730 192 256) v_8728)))));
      pure ()
    pat_end;
    pattern fun (v_3423 : reg (bv 128)) (v_3421 : reg (bv 256)) (v_3422 : reg (bv 256)) => do
      v_8749 <- getRegister v_3423;
      v_8750 <- eval (extract v_8749 64 128);
      v_8752 <- getRegister v_3421;
      setRegister (lhs.of_reg v_3422) (mux (ugt v_8750 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8752 0 64) v_8750) (concat (lshr (extract v_8752 64 128) v_8750) (concat (lshr (extract v_8752 128 192) v_8750) (lshr (extract v_8752 192 256) v_8750)))));
      pure ()
    pat_end;
    pattern fun (v_3398 : Mem) (v_3399 : reg (bv 128)) (v_3400 : reg (bv 128)) => do
      v_14478 <- evaluateAddress v_3398;
      v_14479 <- load v_14478 16;
      v_14480 <- eval (extract v_14479 64 128);
      v_14482 <- getRegister v_3399;
      setRegister (lhs.of_reg v_3400) (mux (ugt v_14480 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14482 0 64) v_14480) (lshr (extract v_14482 64 128) v_14480)));
      pure ()
    pat_end;
    pattern fun (v_3415 : Mem) (v_3416 : reg (bv 256)) (v_3417 : reg (bv 256)) => do
      v_14490 <- evaluateAddress v_3415;
      v_14491 <- load v_14490 16;
      v_14492 <- eval (extract v_14491 64 128);
      v_14494 <- getRegister v_3416;
      setRegister (lhs.of_reg v_3417) (mux (ugt v_14492 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_14494 0 64) v_14492) (concat (lshr (extract v_14494 64 128) v_14492) (concat (lshr (extract v_14494 128 192) v_14492) (lshr (extract v_14494 192 256) v_14492)))));
      pure ()
    pat_end
