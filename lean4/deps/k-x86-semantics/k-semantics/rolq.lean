def rolq1 : instruction :=
  definst "rolq" $ do
    pattern fun (_ : clReg) (v_2710 : reg (bv 64)) => do
      v_4778 <- getRegister rcx;
      v_4780 <- eval (bv_and (extract v_4778 56 64) (expression.bv_nat 8 63));
      v_4782 <- getRegister v_2710;
      v_4784 <- eval (rol v_4782 (concat (expression.bv_nat 56 0) v_4780));
      v_4786 <- eval (isBitSet v_4784 63);
      v_4789 <- eval (eq v_4780 (expression.bv_nat 8 0));
      v_4790 <- getRegister of;
      v_4793 <- getRegister cf;
      setRegister (lhs.of_reg v_2710) v_4784;
      setRegister cf (mux v_4789 v_4793 v_4786);
      setRegister of (mux (eq v_4780 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4784 0) v_4786)) (mux v_4789 v_4790 undef));
      pure ()
    pat_end;
    pattern fun (v_2715 : imm int) (v_2714 : reg (bv 64)) => do
      v_4799 <- eval (bv_and (handleImmediateWithSignExtend v_2715 8 8) (expression.bv_nat 8 63));
      v_4801 <- getRegister v_2714;
      v_4803 <- eval (rol v_4801 (concat (expression.bv_nat 56 0) v_4799));
      v_4805 <- eval (isBitSet v_4803 63);
      v_4808 <- eval (eq v_4799 (expression.bv_nat 8 0));
      v_4809 <- getRegister of;
      v_4812 <- getRegister cf;
      setRegister (lhs.of_reg v_2714) v_4803;
      setRegister cf (mux v_4808 v_4812 v_4805);
      setRegister of (mux (eq v_4799 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4803 0) v_4805)) (mux v_4808 v_4809 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2700 : Mem) => do
      v_11471 <- evaluateAddress v_2700;
      v_11472 <- load v_11471 8;
      v_11473 <- getRegister rcx;
      v_11475 <- eval (bv_and (extract v_11473 56 64) (expression.bv_nat 8 63));
      v_11477 <- eval (rol v_11472 (concat (expression.bv_nat 56 0) v_11475));
      store v_11471 v_11477 8;
      v_11481 <- eval (isBitSet v_11477 63);
      v_11484 <- eval (eq v_11475 (expression.bv_nat 8 0));
      v_11485 <- getRegister of;
      v_11488 <- getRegister cf;
      setRegister cf (mux v_11484 v_11488 v_11481);
      setRegister of (mux (eq v_11475 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11477 0) v_11481)) (mux v_11484 v_11485 undef));
      pure ()
    pat_end;
    pattern fun (v_2703 : imm int) (v_2704 : Mem) => do
      v_11492 <- evaluateAddress v_2704;
      v_11493 <- load v_11492 8;
      v_11495 <- eval (bv_and (handleImmediateWithSignExtend v_2703 8 8) (expression.bv_nat 8 63));
      v_11497 <- eval (rol v_11493 (concat (expression.bv_nat 56 0) v_11495));
      store v_11492 v_11497 8;
      v_11501 <- eval (isBitSet v_11497 63);
      v_11504 <- eval (eq v_11495 (expression.bv_nat 8 0));
      v_11505 <- getRegister of;
      v_11508 <- getRegister cf;
      setRegister cf (mux v_11504 v_11508 v_11501);
      setRegister of (mux (eq v_11495 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11497 0) v_11501)) (mux v_11504 v_11505 undef));
      pure ()
    pat_end
