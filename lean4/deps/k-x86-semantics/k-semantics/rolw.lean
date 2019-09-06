def rolw1 : instruction :=
  definst "rolw" $ do
    pattern fun (_ : clReg) (v_2735 : reg (bv 16)) => do
      v_4836 <- getRegister rcx;
      v_4838 <- eval (bv_and (extract v_4836 56 64) (expression.bv_nat 8 31));
      v_4840 <- getRegister v_2735;
      v_4842 <- eval (rol v_4840 (concat (expression.bv_nat 8 0) v_4838));
      v_4844 <- eval (isBitSet v_4842 15);
      v_4847 <- eval (eq v_4838 (expression.bv_nat 8 0));
      v_4848 <- getRegister of;
      v_4851 <- getRegister cf;
      setRegister (lhs.of_reg v_2735) v_4842;
      setRegister cf (mux v_4847 v_4851 v_4844);
      setRegister of (mux (eq v_4838 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4842 0) v_4844)) (mux v_4847 v_4848 undef));
      pure ()
    pat_end;
    pattern fun (v_2737 : imm int) (v_2740 : reg (bv 16)) => do
      v_4857 <- eval (bv_and (handleImmediateWithSignExtend v_2737 8 8) (expression.bv_nat 8 31));
      v_4859 <- getRegister v_2740;
      v_4861 <- eval (rol v_4859 (concat (expression.bv_nat 8 0) v_4857));
      v_4863 <- eval (isBitSet v_4861 15);
      v_4866 <- eval (eq v_4857 (expression.bv_nat 8 0));
      v_4867 <- getRegister of;
      v_4870 <- getRegister cf;
      setRegister (lhs.of_reg v_2740) v_4861;
      setRegister cf (mux v_4866 v_4870 v_4863);
      setRegister of (mux (eq v_4857 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4861 0) v_4863)) (mux v_4866 v_4867 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2723 : Mem) => do
      v_11532 <- evaluateAddress v_2723;
      v_11533 <- load v_11532 2;
      v_11534 <- getRegister rcx;
      v_11536 <- eval (bv_and (extract v_11534 56 64) (expression.bv_nat 8 31));
      v_11538 <- eval (rol v_11533 (concat (expression.bv_nat 8 0) v_11536));
      store v_11532 v_11538 2;
      v_11542 <- eval (isBitSet v_11538 15);
      v_11545 <- eval (eq v_11536 (expression.bv_nat 8 0));
      v_11546 <- getRegister of;
      v_11549 <- getRegister cf;
      setRegister cf (mux v_11545 v_11549 v_11542);
      setRegister of (mux (eq v_11536 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11538 0) v_11542)) (mux v_11545 v_11546 undef));
      pure ()
    pat_end;
    pattern fun (v_2726 : imm int) (v_2727 : Mem) => do
      v_11553 <- evaluateAddress v_2727;
      v_11554 <- load v_11553 2;
      v_11556 <- eval (bv_and (handleImmediateWithSignExtend v_2726 8 8) (expression.bv_nat 8 31));
      v_11558 <- eval (rol v_11554 (concat (expression.bv_nat 8 0) v_11556));
      store v_11553 v_11558 2;
      v_11562 <- eval (isBitSet v_11558 15);
      v_11565 <- eval (eq v_11556 (expression.bv_nat 8 0));
      v_11566 <- getRegister of;
      v_11569 <- getRegister cf;
      setRegister cf (mux v_11565 v_11569 v_11562);
      setRegister of (mux (eq v_11556 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11558 0) v_11562)) (mux v_11565 v_11566 undef));
      pure ()
    pat_end
