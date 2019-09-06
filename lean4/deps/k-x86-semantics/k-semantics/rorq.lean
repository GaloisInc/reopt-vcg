def rorq1 : instruction :=
  definst "rorq" $ do
    pattern fun (_ : clReg) (v_2815 : reg (bv 64)) => do
      v_5054 <- getRegister rcx;
      v_5056 <- eval (bv_and (extract v_5054 56 64) (expression.bv_nat 8 63));
      v_5058 <- getRegister v_2815;
      v_5060 <- eval (ror v_5058 (concat (expression.bv_nat 56 0) v_5056));
      v_5061 <- eval (isBitSet v_5060 0);
      v_5065 <- eval (eq v_5056 (expression.bv_nat 8 0));
      v_5066 <- getRegister of;
      v_5069 <- getRegister cf;
      setRegister (lhs.of_reg v_2815) v_5060;
      setRegister cf (mux v_5065 v_5069 v_5061);
      setRegister of (mux (eq v_5056 (expression.bv_nat 8 1)) (notBool_ (eq v_5061 (isBitSet v_5060 1))) (mux v_5065 v_5066 undef));
      pure ()
    pat_end;
    pattern fun (v_2820 : imm int) (v_2819 : reg (bv 64)) => do
      v_5075 <- eval (bv_and (handleImmediateWithSignExtend v_2820 8 8) (expression.bv_nat 8 63));
      v_5077 <- getRegister v_2819;
      v_5079 <- eval (ror v_5077 (concat (expression.bv_nat 56 0) v_5075));
      v_5080 <- eval (isBitSet v_5079 0);
      v_5084 <- eval (eq v_5075 (expression.bv_nat 8 0));
      v_5085 <- getRegister of;
      v_5088 <- getRegister cf;
      setRegister (lhs.of_reg v_2819) v_5079;
      setRegister cf (mux v_5084 v_5088 v_5080);
      setRegister of (mux (eq v_5075 (expression.bv_nat 8 1)) (notBool_ (eq v_5080 (isBitSet v_5079 1))) (mux v_5084 v_5085 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2805 : Mem) => do
      v_11713 <- evaluateAddress v_2805;
      v_11714 <- load v_11713 8;
      v_11715 <- getRegister rcx;
      v_11717 <- eval (bv_and (extract v_11715 56 64) (expression.bv_nat 8 63));
      v_11719 <- eval (ror v_11714 (concat (expression.bv_nat 56 0) v_11717));
      store v_11713 v_11719 8;
      v_11722 <- eval (isBitSet v_11719 0);
      v_11726 <- eval (eq v_11717 (expression.bv_nat 8 0));
      v_11727 <- getRegister of;
      v_11730 <- getRegister cf;
      setRegister cf (mux v_11726 v_11730 v_11722);
      setRegister of (mux (eq v_11717 (expression.bv_nat 8 1)) (notBool_ (eq v_11722 (isBitSet v_11719 1))) (mux v_11726 v_11727 undef));
      pure ()
    pat_end;
    pattern fun (v_2808 : imm int) (v_2809 : Mem) => do
      v_11734 <- evaluateAddress v_2809;
      v_11735 <- load v_11734 8;
      v_11737 <- eval (bv_and (handleImmediateWithSignExtend v_2808 8 8) (expression.bv_nat 8 63));
      v_11739 <- eval (ror v_11735 (concat (expression.bv_nat 56 0) v_11737));
      store v_11734 v_11739 8;
      v_11742 <- eval (isBitSet v_11739 0);
      v_11746 <- eval (eq v_11737 (expression.bv_nat 8 0));
      v_11747 <- getRegister of;
      v_11750 <- getRegister cf;
      setRegister cf (mux v_11746 v_11750 v_11742);
      setRegister of (mux (eq v_11737 (expression.bv_nat 8 1)) (notBool_ (eq v_11742 (isBitSet v_11739 1))) (mux v_11746 v_11747 undef));
      pure ()
    pat_end
