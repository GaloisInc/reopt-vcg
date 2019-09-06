def rorw1 : instruction :=
  definst "rorw" $ do
    pattern fun (_ : clReg) (v_2840 : reg (bv 16)) => do
      v_5112 <- getRegister rcx;
      v_5114 <- eval (bv_and (extract v_5112 56 64) (expression.bv_nat 8 31));
      v_5116 <- getRegister v_2840;
      v_5118 <- eval (ror v_5116 (concat (expression.bv_nat 8 0) v_5114));
      v_5119 <- eval (isBitSet v_5118 0);
      v_5123 <- eval (eq v_5114 (expression.bv_nat 8 0));
      v_5124 <- getRegister of;
      v_5127 <- getRegister cf;
      setRegister (lhs.of_reg v_2840) v_5118;
      setRegister cf (mux v_5123 v_5127 v_5119);
      setRegister of (mux (eq v_5114 (expression.bv_nat 8 1)) (notBool_ (eq v_5119 (isBitSet v_5118 1))) (mux v_5123 v_5124 undef));
      pure ()
    pat_end;
    pattern fun (v_2842 : imm int) (v_2845 : reg (bv 16)) => do
      v_5133 <- eval (bv_and (handleImmediateWithSignExtend v_2842 8 8) (expression.bv_nat 8 31));
      v_5135 <- getRegister v_2845;
      v_5137 <- eval (ror v_5135 (concat (expression.bv_nat 8 0) v_5133));
      v_5138 <- eval (isBitSet v_5137 0);
      v_5142 <- eval (eq v_5133 (expression.bv_nat 8 0));
      v_5143 <- getRegister of;
      v_5146 <- getRegister cf;
      setRegister (lhs.of_reg v_2845) v_5137;
      setRegister cf (mux v_5142 v_5146 v_5138);
      setRegister of (mux (eq v_5133 (expression.bv_nat 8 1)) (notBool_ (eq v_5138 (isBitSet v_5137 1))) (mux v_5142 v_5143 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2828 : Mem) => do
      v_11774 <- evaluateAddress v_2828;
      v_11775 <- load v_11774 2;
      v_11776 <- getRegister rcx;
      v_11778 <- eval (bv_and (extract v_11776 56 64) (expression.bv_nat 8 31));
      v_11780 <- eval (ror v_11775 (concat (expression.bv_nat 8 0) v_11778));
      store v_11774 v_11780 2;
      v_11783 <- eval (isBitSet v_11780 0);
      v_11787 <- eval (eq v_11778 (expression.bv_nat 8 0));
      v_11788 <- getRegister of;
      v_11791 <- getRegister cf;
      setRegister cf (mux v_11787 v_11791 v_11783);
      setRegister of (mux (eq v_11778 (expression.bv_nat 8 1)) (notBool_ (eq v_11783 (isBitSet v_11780 1))) (mux v_11787 v_11788 undef));
      pure ()
    pat_end;
    pattern fun (v_2831 : imm int) (v_2832 : Mem) => do
      v_11795 <- evaluateAddress v_2832;
      v_11796 <- load v_11795 2;
      v_11798 <- eval (bv_and (handleImmediateWithSignExtend v_2831 8 8) (expression.bv_nat 8 31));
      v_11800 <- eval (ror v_11796 (concat (expression.bv_nat 8 0) v_11798));
      store v_11795 v_11800 2;
      v_11803 <- eval (isBitSet v_11800 0);
      v_11807 <- eval (eq v_11798 (expression.bv_nat 8 0));
      v_11808 <- getRegister of;
      v_11811 <- getRegister cf;
      setRegister cf (mux v_11807 v_11811 v_11803);
      setRegister of (mux (eq v_11798 (expression.bv_nat 8 1)) (notBool_ (eq v_11803 (isBitSet v_11800 1))) (mux v_11807 v_11808 undef));
      pure ()
    pat_end
