def vpsrlq1 : instruction :=
  definst "vpsrlq" $ do
    pattern fun (v_3419 : imm int) (v_3421 : reg (bv 128)) (v_3422 : reg (bv 128)) => do
      v_8728 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3419 8 8));
      v_8730 <- getRegister v_3421;
      setRegister (lhs.of_reg v_3422) (mux (ugt v_8728 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8730 0 64) v_8728) (lshr (extract v_8730 64 128) v_8728)));
      pure ()
    pat_end;
    pattern fun (v_3431 : reg (bv 128)) (v_3432 : reg (bv 128)) (v_3433 : reg (bv 128)) => do
      v_8743 <- getRegister v_3431;
      v_8744 <- eval (extract v_8743 64 128);
      v_8746 <- getRegister v_3432;
      setRegister (lhs.of_reg v_3433) (mux (ugt v_8744 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8746 0 64) v_8744) (lshr (extract v_8746 64 128) v_8744)));
      pure ()
    pat_end;
    pattern fun (v_3436 : imm int) (v_3438 : reg (bv 256)) (v_3439 : reg (bv 256)) => do
      v_8755 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3436 8 8));
      v_8757 <- getRegister v_3438;
      setRegister (lhs.of_reg v_3439) (mux (ugt v_8755 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8757 0 64) v_8755) (concat (lshr (extract v_8757 64 128) v_8755) (concat (lshr (extract v_8757 128 192) v_8755) (lshr (extract v_8757 192 256) v_8755)))));
      pure ()
    pat_end;
    pattern fun (v_3450 : reg (bv 128)) (v_3448 : reg (bv 256)) (v_3449 : reg (bv 256)) => do
      v_8776 <- getRegister v_3450;
      v_8777 <- eval (extract v_8776 64 128);
      v_8779 <- getRegister v_3448;
      setRegister (lhs.of_reg v_3449) (mux (ugt v_8777 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8779 0 64) v_8777) (concat (lshr (extract v_8779 64 128) v_8777) (concat (lshr (extract v_8779 128 192) v_8777) (lshr (extract v_8779 192 256) v_8777)))));
      pure ()
    pat_end;
    pattern fun (v_3425 : Mem) (v_3426 : reg (bv 128)) (v_3427 : reg (bv 128)) => do
      v_14505 <- evaluateAddress v_3425;
      v_14506 <- load v_14505 16;
      v_14507 <- eval (extract v_14506 64 128);
      v_14509 <- getRegister v_3426;
      setRegister (lhs.of_reg v_3427) (mux (ugt v_14507 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14509 0 64) v_14507) (lshr (extract v_14509 64 128) v_14507)));
      pure ()
    pat_end;
    pattern fun (v_3442 : Mem) (v_3443 : reg (bv 256)) (v_3444 : reg (bv 256)) => do
      v_14517 <- evaluateAddress v_3442;
      v_14518 <- load v_14517 16;
      v_14519 <- eval (extract v_14518 64 128);
      v_14521 <- getRegister v_3443;
      setRegister (lhs.of_reg v_3444) (mux (ugt v_14519 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_14521 0 64) v_14519) (concat (lshr (extract v_14521 64 128) v_14519) (concat (lshr (extract v_14521 128 192) v_14519) (lshr (extract v_14521 192 256) v_14519)))));
      pure ()
    pat_end
