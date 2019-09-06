def rorl1 : instruction :=
  definst "rorl" $ do
    pattern fun (_ : clReg) (v_2794 : reg (bv 32)) => do
      v_4996 <- getRegister rcx;
      v_4998 <- eval (bv_and (extract v_4996 56 64) (expression.bv_nat 8 31));
      v_5000 <- getRegister v_2794;
      v_5002 <- eval (ror v_5000 (concat (expression.bv_nat 24 0) v_4998));
      v_5003 <- eval (isBitSet v_5002 0);
      v_5007 <- eval (eq v_4998 (expression.bv_nat 8 0));
      v_5008 <- getRegister of;
      v_5011 <- getRegister cf;
      setRegister (lhs.of_reg v_2794) v_5002;
      setRegister cf (mux v_5007 v_5011 v_5003);
      setRegister of (mux (eq v_4998 (expression.bv_nat 8 1)) (notBool_ (eq v_5003 (isBitSet v_5002 1))) (mux v_5007 v_5008 undef));
      pure ()
    pat_end;
    pattern fun (v_2796 : imm int) (v_2799 : reg (bv 32)) => do
      v_5017 <- eval (bv_and (handleImmediateWithSignExtend v_2796 8 8) (expression.bv_nat 8 31));
      v_5019 <- getRegister v_2799;
      v_5021 <- eval (ror v_5019 (concat (expression.bv_nat 24 0) v_5017));
      v_5022 <- eval (isBitSet v_5021 0);
      v_5026 <- eval (eq v_5017 (expression.bv_nat 8 0));
      v_5027 <- getRegister of;
      v_5030 <- getRegister cf;
      setRegister (lhs.of_reg v_2799) v_5021;
      setRegister cf (mux v_5026 v_5030 v_5022);
      setRegister of (mux (eq v_5017 (expression.bv_nat 8 1)) (notBool_ (eq v_5022 (isBitSet v_5021 1))) (mux v_5026 v_5027 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2782 : Mem) => do
      v_11652 <- evaluateAddress v_2782;
      v_11653 <- load v_11652 4;
      v_11654 <- getRegister rcx;
      v_11656 <- eval (bv_and (extract v_11654 56 64) (expression.bv_nat 8 31));
      v_11658 <- eval (ror v_11653 (concat (expression.bv_nat 24 0) v_11656));
      store v_11652 v_11658 4;
      v_11661 <- eval (isBitSet v_11658 0);
      v_11665 <- eval (eq v_11656 (expression.bv_nat 8 0));
      v_11666 <- getRegister of;
      v_11669 <- getRegister cf;
      setRegister cf (mux v_11665 v_11669 v_11661);
      setRegister of (mux (eq v_11656 (expression.bv_nat 8 1)) (notBool_ (eq v_11661 (isBitSet v_11658 1))) (mux v_11665 v_11666 undef));
      pure ()
    pat_end;
    pattern fun (v_2785 : imm int) (v_2786 : Mem) => do
      v_11673 <- evaluateAddress v_2786;
      v_11674 <- load v_11673 4;
      v_11676 <- eval (bv_and (handleImmediateWithSignExtend v_2785 8 8) (expression.bv_nat 8 31));
      v_11678 <- eval (ror v_11674 (concat (expression.bv_nat 24 0) v_11676));
      store v_11673 v_11678 4;
      v_11681 <- eval (isBitSet v_11678 0);
      v_11685 <- eval (eq v_11676 (expression.bv_nat 8 0));
      v_11686 <- getRegister of;
      v_11689 <- getRegister cf;
      setRegister cf (mux v_11685 v_11689 v_11681);
      setRegister of (mux (eq v_11676 (expression.bv_nat 8 1)) (notBool_ (eq v_11681 (isBitSet v_11678 1))) (mux v_11685 v_11686 undef));
      pure ()
    pat_end
