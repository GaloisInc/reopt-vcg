def shlw1 : instruction :=
  definst "shlw" $ do
    pattern fun (_ : clReg) (v_2893 : reg (bv 16)) => do
      v_4717 <- getRegister rcx;
      v_4719 <- eval (bv_and (extract v_4717 56 64) (expression.bv_nat 8 31));
      v_4720 <- eval (eq v_4719 (expression.bv_nat 8 0));
      v_4721 <- getRegister zf;
      v_4722 <- getRegister v_2893;
      v_4726 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4722) (concat (expression.bv_nat 9 0) v_4719)) 0 17);
      v_4727 <- eval (extract v_4726 1 17);
      v_4730 <- getRegister sf;
      v_4731 <- eval (isBitSet v_4726 1);
      v_4733 <- getRegister pf;
      v_4739 <- getRegister cf;
      v_4742 <- eval (mux (uge v_4719 (expression.bv_nat 8 16)) undef (mux v_4720 v_4739 (isBitSet v_4726 0)));
      v_4745 <- getRegister of;
      v_4748 <- getRegister af;
      setRegister (lhs.of_reg v_2893) v_4727;
      setRegister af (mux v_4720 v_4748 undef);
      setRegister cf v_4742;
      setRegister of (mux (eq v_4719 (expression.bv_nat 8 1)) (notBool_ (eq v_4742 v_4731)) (mux v_4720 v_4745 undef));
      setRegister pf (mux v_4720 v_4733 (parityFlag (extract v_4726 9 17)));
      setRegister sf (mux v_4720 v_4730 v_4731);
      setRegister zf (mux v_4720 v_4721 (eq v_4727 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_2897 : imm int) (v_2898 : reg (bv 16)) => do
      v_4758 <- eval (bv_and (handleImmediateWithSignExtend v_2897 8 8) (expression.bv_nat 8 31));
      v_4759 <- eval (eq v_4758 (expression.bv_nat 8 0));
      v_4760 <- getRegister zf;
      v_4761 <- getRegister v_2898;
      v_4765 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4761) (concat (expression.bv_nat 9 0) v_4758)) 0 17);
      v_4766 <- eval (extract v_4765 1 17);
      v_4769 <- getRegister sf;
      v_4770 <- eval (isBitSet v_4765 1);
      v_4772 <- getRegister pf;
      v_4778 <- getRegister cf;
      v_4781 <- eval (mux (uge v_4758 (expression.bv_nat 8 16)) undef (mux v_4759 v_4778 (isBitSet v_4765 0)));
      v_4784 <- getRegister of;
      v_4787 <- getRegister af;
      setRegister (lhs.of_reg v_2898) v_4766;
      setRegister af (mux v_4759 v_4787 undef);
      setRegister cf v_4781;
      setRegister of (mux (eq v_4758 (expression.bv_nat 8 1)) (notBool_ (eq v_4781 v_4770)) (mux v_4759 v_4784 undef));
      setRegister pf (mux v_4759 v_4772 (parityFlag (extract v_4765 9 17)));
      setRegister sf (mux v_4759 v_4769 v_4770);
      setRegister zf (mux v_4759 v_4760 (eq v_4766 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2883 : Mem) => do
      v_9179 <- evaluateAddress v_2883;
      v_9180 <- load v_9179 2;
      v_9182 <- getRegister rcx;
      v_9184 <- eval (bv_and (extract v_9182 56 64) (expression.bv_nat 8 31));
      v_9187 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9180) (concat (expression.bv_nat 9 0) v_9184)) 0 17);
      v_9188 <- eval (extract v_9187 1 17);
      store v_9179 v_9188 2;
      v_9190 <- eval (eq v_9184 (expression.bv_nat 8 0));
      v_9191 <- getRegister zf;
      v_9194 <- getRegister sf;
      v_9195 <- eval (isBitSet v_9187 1);
      v_9197 <- getRegister pf;
      v_9203 <- getRegister cf;
      v_9206 <- eval (mux (uge v_9184 (expression.bv_nat 8 16)) undef (mux v_9190 v_9203 (isBitSet v_9187 0)));
      v_9209 <- getRegister of;
      v_9212 <- getRegister af;
      setRegister af (mux v_9190 v_9212 undef);
      setRegister cf v_9206;
      setRegister of (mux (eq v_9184 (expression.bv_nat 8 1)) (notBool_ (eq v_9206 v_9195)) (mux v_9190 v_9209 undef));
      setRegister pf (mux v_9190 v_9197 (parityFlag (extract v_9187 9 17)));
      setRegister sf (mux v_9190 v_9194 v_9195);
      setRegister zf (mux v_9190 v_9191 (eq v_9188 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_2887 : imm int) (v_2886 : Mem) => do
      v_9220 <- evaluateAddress v_2886;
      v_9221 <- load v_9220 2;
      v_9224 <- eval (bv_and (handleImmediateWithSignExtend v_2887 8 8) (expression.bv_nat 8 31));
      v_9227 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9221) (concat (expression.bv_nat 9 0) v_9224)) 0 17);
      v_9228 <- eval (extract v_9227 1 17);
      store v_9220 v_9228 2;
      v_9230 <- eval (eq v_9224 (expression.bv_nat 8 0));
      v_9231 <- getRegister zf;
      v_9234 <- getRegister sf;
      v_9235 <- eval (isBitSet v_9227 1);
      v_9237 <- getRegister pf;
      v_9243 <- getRegister cf;
      v_9246 <- eval (mux (uge v_9224 (expression.bv_nat 8 16)) undef (mux v_9230 v_9243 (isBitSet v_9227 0)));
      v_9249 <- getRegister of;
      v_9252 <- getRegister af;
      setRegister af (mux v_9230 v_9252 undef);
      setRegister cf v_9246;
      setRegister of (mux (eq v_9224 (expression.bv_nat 8 1)) (notBool_ (eq v_9246 v_9235)) (mux v_9230 v_9249 undef));
      setRegister pf (mux v_9230 v_9237 (parityFlag (extract v_9227 9 17)));
      setRegister sf (mux v_9230 v_9234 v_9235);
      setRegister zf (mux v_9230 v_9231 (eq v_9228 (expression.bv_nat 16 0)));
      pure ()
    pat_end
