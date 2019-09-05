def vpsrld1 : instruction :=
  definst "vpsrld" $ do
    pattern fun (v_3344 : imm int) (v_3348 : reg (bv 128)) (v_3349 : reg (bv 128)) => do
      v_8572 <- eval (handleImmediateWithSignExtend v_3344 8 8);
      v_8575 <- getRegister v_3348;
      v_8577 <- eval (concat (expression.bv_nat 24 0) v_8572);
      setRegister (lhs.of_reg v_3349) (mux (ugt (concat (expression.bv_nat 56 0) v_8572) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8575 0 32) v_8577) (concat (lshr (extract v_8575 32 64) v_8577) (concat (lshr (extract v_8575 64 96) v_8577) (lshr (extract v_8575 96 128) v_8577)))));
      pure ()
    pat_end;
    pattern fun (v_3358 : reg (bv 128)) (v_3359 : reg (bv 128)) (v_3360 : reg (bv 128)) => do
      v_8595 <- getRegister v_3358;
      v_8598 <- getRegister v_3359;
      v_8600 <- eval (extract v_8595 96 128);
      setRegister (lhs.of_reg v_3360) (mux (ugt (extract v_8595 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8598 0 32) v_8600) (concat (lshr (extract v_8598 32 64) v_8600) (concat (lshr (extract v_8598 64 96) v_8600) (lshr (extract v_8598 96 128) v_8600)))));
      pure ()
    pat_end;
    pattern fun (v_3361 : imm int) (v_3365 : reg (bv 256)) (v_3366 : reg (bv 256)) => do
      v_8613 <- eval (handleImmediateWithSignExtend v_3361 8 8);
      v_8616 <- getRegister v_3365;
      v_8618 <- eval (concat (expression.bv_nat 24 0) v_8613);
      setRegister (lhs.of_reg v_3366) (mux (ugt (concat (expression.bv_nat 56 0) v_8613) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8616 0 32) v_8618) (concat (lshr (extract v_8616 32 64) v_8618) (concat (lshr (extract v_8616 64 96) v_8618) (concat (lshr (extract v_8616 96 128) v_8618) (concat (lshr (extract v_8616 128 160) v_8618) (concat (lshr (extract v_8616 160 192) v_8618) (concat (lshr (extract v_8616 192 224) v_8618) (lshr (extract v_8616 224 256) v_8618)))))))));
      pure ()
    pat_end;
    pattern fun (v_3377 : reg (bv 128)) (v_3375 : reg (bv 256)) (v_3376 : reg (bv 256)) => do
      v_8648 <- getRegister v_3377;
      v_8651 <- getRegister v_3375;
      v_8653 <- eval (extract v_8648 96 128);
      setRegister (lhs.of_reg v_3376) (mux (ugt (extract v_8648 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_8651 0 32) v_8653) (concat (lshr (extract v_8651 32 64) v_8653) (concat (lshr (extract v_8651 64 96) v_8653) (concat (lshr (extract v_8651 96 128) v_8653) (concat (lshr (extract v_8651 128 160) v_8653) (concat (lshr (extract v_8651 160 192) v_8653) (concat (lshr (extract v_8651 192 224) v_8653) (lshr (extract v_8651 224 256) v_8653)))))))));
      pure ()
    pat_end;
    pattern fun (v_3352 : Mem) (v_3353 : reg (bv 128)) (v_3354 : reg (bv 128)) => do
      v_14428 <- evaluateAddress v_3352;
      v_14429 <- load v_14428 16;
      v_14432 <- getRegister v_3353;
      v_14434 <- eval (extract v_14429 96 128);
      setRegister (lhs.of_reg v_3354) (mux (ugt (extract v_14429 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14432 0 32) v_14434) (concat (lshr (extract v_14432 32 64) v_14434) (concat (lshr (extract v_14432 64 96) v_14434) (lshr (extract v_14432 96 128) v_14434)))));
      pure ()
    pat_end;
    pattern fun (v_3369 : Mem) (v_3370 : reg (bv 256)) (v_3371 : reg (bv 256)) => do
      v_14447 <- evaluateAddress v_3369;
      v_14448 <- load v_14447 16;
      v_14451 <- getRegister v_3370;
      v_14453 <- eval (extract v_14448 96 128);
      setRegister (lhs.of_reg v_3371) (mux (ugt (extract v_14448 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_14451 0 32) v_14453) (concat (lshr (extract v_14451 32 64) v_14453) (concat (lshr (extract v_14451 64 96) v_14453) (concat (lshr (extract v_14451 96 128) v_14453) (concat (lshr (extract v_14451 128 160) v_14453) (concat (lshr (extract v_14451 160 192) v_14453) (concat (lshr (extract v_14451 192 224) v_14453) (lshr (extract v_14451 224 256) v_14453)))))))));
      pure ()
    pat_end
