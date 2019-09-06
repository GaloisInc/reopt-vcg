def shlq1 : instruction :=
  definst "shlq" $ do
    pattern fun (_ : clReg) (v_2870 : reg (bv 64)) => do
      v_4609 <- getRegister rcx;
      v_4611 <- eval (bv_and (extract v_4609 56 64) (expression.bv_nat 8 63));
      v_4612 <- eval (eq v_4611 (expression.bv_nat 8 0));
      v_4613 <- getRegister zf;
      v_4614 <- getRegister v_2870;
      v_4618 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4614) (concat (expression.bv_nat 57 0) v_4611)) 0 65);
      v_4619 <- eval (extract v_4618 1 65);
      v_4622 <- getRegister sf;
      v_4623 <- eval (isBitSet v_4618 1);
      v_4625 <- getRegister pf;
      v_4631 <- getRegister cf;
      v_4634 <- eval (mux (uge v_4611 (expression.bv_nat 8 64)) undef (mux v_4612 v_4631 (isBitSet v_4618 0)));
      v_4637 <- getRegister of;
      v_4640 <- getRegister af;
      setRegister (lhs.of_reg v_2870) v_4619;
      setRegister af (mux v_4612 v_4640 undef);
      setRegister cf v_4634;
      setRegister of (mux (eq v_4611 (expression.bv_nat 8 1)) (notBool_ (eq v_4634 v_4623)) (mux v_4612 v_4637 undef));
      setRegister pf (mux v_4612 v_4625 (parityFlag (extract v_4618 57 65)));
      setRegister sf (mux v_4612 v_4622 v_4623);
      setRegister zf (mux v_4612 v_4613 (eq v_4619 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2874 : imm int) (v_2875 : reg (bv 64)) => do
      v_4650 <- eval (bv_and (handleImmediateWithSignExtend v_2874 8 8) (expression.bv_nat 8 63));
      v_4651 <- eval (eq v_4650 (expression.bv_nat 8 0));
      v_4652 <- getRegister zf;
      v_4653 <- getRegister v_2875;
      v_4657 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4653) (concat (expression.bv_nat 57 0) v_4650)) 0 65);
      v_4658 <- eval (extract v_4657 1 65);
      v_4661 <- getRegister sf;
      v_4662 <- eval (isBitSet v_4657 1);
      v_4664 <- getRegister pf;
      v_4670 <- getRegister cf;
      v_4673 <- eval (mux (uge v_4650 (expression.bv_nat 8 64)) undef (mux v_4651 v_4670 (isBitSet v_4657 0)));
      v_4676 <- getRegister of;
      v_4679 <- getRegister af;
      setRegister (lhs.of_reg v_2875) v_4658;
      setRegister af (mux v_4651 v_4679 undef);
      setRegister cf v_4673;
      setRegister of (mux (eq v_4650 (expression.bv_nat 8 1)) (notBool_ (eq v_4673 v_4662)) (mux v_4651 v_4676 undef));
      setRegister pf (mux v_4651 v_4664 (parityFlag (extract v_4657 57 65)));
      setRegister sf (mux v_4651 v_4661 v_4662);
      setRegister zf (mux v_4651 v_4652 (eq v_4658 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2860 : Mem) => do
      v_9058 <- evaluateAddress v_2860;
      v_9059 <- load v_9058 8;
      v_9061 <- getRegister rcx;
      v_9063 <- eval (bv_and (extract v_9061 56 64) (expression.bv_nat 8 63));
      v_9066 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9059) (concat (expression.bv_nat 57 0) v_9063)) 0 65);
      v_9067 <- eval (extract v_9066 1 65);
      store v_9058 v_9067 8;
      v_9069 <- eval (eq v_9063 (expression.bv_nat 8 0));
      v_9070 <- getRegister zf;
      v_9073 <- getRegister sf;
      v_9074 <- eval (isBitSet v_9066 1);
      v_9076 <- getRegister pf;
      v_9082 <- getRegister cf;
      v_9085 <- eval (mux (uge v_9063 (expression.bv_nat 8 64)) undef (mux v_9069 v_9082 (isBitSet v_9066 0)));
      v_9088 <- getRegister of;
      v_9091 <- getRegister af;
      setRegister af (mux v_9069 v_9091 undef);
      setRegister cf v_9085;
      setRegister of (mux (eq v_9063 (expression.bv_nat 8 1)) (notBool_ (eq v_9085 v_9074)) (mux v_9069 v_9088 undef));
      setRegister pf (mux v_9069 v_9076 (parityFlag (extract v_9066 57 65)));
      setRegister sf (mux v_9069 v_9073 v_9074);
      setRegister zf (mux v_9069 v_9070 (eq v_9067 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2864 : imm int) (v_2863 : Mem) => do
      v_9099 <- evaluateAddress v_2863;
      v_9100 <- load v_9099 8;
      v_9103 <- eval (bv_and (handleImmediateWithSignExtend v_2864 8 8) (expression.bv_nat 8 63));
      v_9106 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9100) (concat (expression.bv_nat 57 0) v_9103)) 0 65);
      v_9107 <- eval (extract v_9106 1 65);
      store v_9099 v_9107 8;
      v_9109 <- eval (eq v_9103 (expression.bv_nat 8 0));
      v_9110 <- getRegister zf;
      v_9113 <- getRegister sf;
      v_9114 <- eval (isBitSet v_9106 1);
      v_9116 <- getRegister pf;
      v_9122 <- getRegister cf;
      v_9125 <- eval (mux (uge v_9103 (expression.bv_nat 8 64)) undef (mux v_9109 v_9122 (isBitSet v_9106 0)));
      v_9128 <- getRegister of;
      v_9131 <- getRegister af;
      setRegister af (mux v_9109 v_9131 undef);
      setRegister cf v_9125;
      setRegister of (mux (eq v_9103 (expression.bv_nat 8 1)) (notBool_ (eq v_9125 v_9114)) (mux v_9109 v_9128 undef));
      setRegister pf (mux v_9109 v_9116 (parityFlag (extract v_9106 57 65)));
      setRegister sf (mux v_9109 v_9113 v_9114);
      setRegister zf (mux v_9109 v_9110 (eq v_9107 (expression.bv_nat 64 0)));
      pure ()
    pat_end
