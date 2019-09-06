def shlb1 : instruction :=
  definst "shlb" $ do
    pattern fun (_ : clReg) (v_2824 : reg (bv 8)) => do
      v_4396 <- getRegister rcx;
      v_4398 <- eval (bv_and (extract v_4396 56 64) (expression.bv_nat 8 31));
      v_4399 <- eval (eq v_4398 (expression.bv_nat 8 0));
      v_4400 <- getRegister zf;
      v_4401 <- getRegister v_2824;
      v_4405 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4401) (concat (expression.bv_nat 1 0) v_4398)) 0 9);
      v_4406 <- eval (extract v_4405 1 9);
      v_4409 <- getRegister sf;
      v_4410 <- eval (isBitSet v_4405 1);
      v_4412 <- getRegister pf;
      v_4417 <- getRegister cf;
      v_4420 <- eval (mux (uge v_4398 (expression.bv_nat 8 8)) undef (mux v_4399 v_4417 (isBitSet v_4405 0)));
      v_4423 <- getRegister of;
      v_4426 <- getRegister af;
      setRegister (lhs.of_reg v_2824) v_4406;
      setRegister af (mux v_4399 v_4426 undef);
      setRegister cf v_4420;
      setRegister of (mux (eq v_4398 (expression.bv_nat 8 1)) (notBool_ (eq v_4420 v_4410)) (mux v_4399 v_4423 undef));
      setRegister pf (mux v_4399 v_4412 (parityFlag v_4406));
      setRegister sf (mux v_4399 v_4409 v_4410);
      setRegister zf (mux v_4399 v_4400 (eq v_4406 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2828 : imm int) (v_2829 : reg (bv 8)) => do
      v_4436 <- eval (bv_and (handleImmediateWithSignExtend v_2828 8 8) (expression.bv_nat 8 31));
      v_4437 <- eval (eq v_4436 (expression.bv_nat 8 0));
      v_4438 <- getRegister zf;
      v_4439 <- getRegister v_2829;
      v_4443 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4439) (concat (expression.bv_nat 1 0) v_4436)) 0 9);
      v_4444 <- eval (extract v_4443 1 9);
      v_4447 <- getRegister sf;
      v_4448 <- eval (isBitSet v_4443 1);
      v_4450 <- getRegister pf;
      v_4455 <- getRegister cf;
      v_4458 <- eval (mux (uge v_4436 (expression.bv_nat 8 8)) undef (mux v_4437 v_4455 (isBitSet v_4443 0)));
      v_4461 <- getRegister of;
      v_4464 <- getRegister af;
      setRegister (lhs.of_reg v_2829) v_4444;
      setRegister af (mux v_4437 v_4464 undef);
      setRegister cf v_4458;
      setRegister of (mux (eq v_4436 (expression.bv_nat 8 1)) (notBool_ (eq v_4458 v_4448)) (mux v_4437 v_4461 undef));
      setRegister pf (mux v_4437 v_4450 (parityFlag v_4444));
      setRegister sf (mux v_4437 v_4447 v_4448);
      setRegister zf (mux v_4437 v_4438 (eq v_4444 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2801 : Mem) => do
      v_8820 <- evaluateAddress v_2801;
      v_8821 <- load v_8820 1;
      v_8823 <- getRegister rcx;
      v_8825 <- eval (bv_and (extract v_8823 56 64) (expression.bv_nat 8 31));
      v_8828 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8821) (concat (expression.bv_nat 1 0) v_8825)) 0 9);
      v_8829 <- eval (extract v_8828 1 9);
      store v_8820 v_8829 1;
      v_8831 <- eval (eq v_8825 (expression.bv_nat 8 0));
      v_8832 <- getRegister zf;
      v_8835 <- getRegister sf;
      v_8836 <- eval (isBitSet v_8828 1);
      v_8838 <- getRegister pf;
      v_8843 <- getRegister cf;
      v_8846 <- eval (mux (uge v_8825 (expression.bv_nat 8 8)) undef (mux v_8831 v_8843 (isBitSet v_8828 0)));
      v_8849 <- getRegister of;
      v_8852 <- getRegister af;
      setRegister af (mux v_8831 v_8852 undef);
      setRegister cf v_8846;
      setRegister of (mux (eq v_8825 (expression.bv_nat 8 1)) (notBool_ (eq v_8846 v_8836)) (mux v_8831 v_8849 undef));
      setRegister pf (mux v_8831 v_8838 (parityFlag v_8829));
      setRegister sf (mux v_8831 v_8835 v_8836);
      setRegister zf (mux v_8831 v_8832 (eq v_8829 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2805 : imm int) (v_2804 : Mem) => do
      v_8860 <- evaluateAddress v_2804;
      v_8861 <- load v_8860 1;
      v_8864 <- eval (bv_and (handleImmediateWithSignExtend v_2805 8 8) (expression.bv_nat 8 31));
      v_8867 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8861) (concat (expression.bv_nat 1 0) v_8864)) 0 9);
      v_8868 <- eval (extract v_8867 1 9);
      store v_8860 v_8868 1;
      v_8870 <- eval (eq v_8864 (expression.bv_nat 8 0));
      v_8871 <- getRegister zf;
      v_8874 <- getRegister sf;
      v_8875 <- eval (isBitSet v_8867 1);
      v_8877 <- getRegister pf;
      v_8882 <- getRegister cf;
      v_8885 <- eval (mux (uge v_8864 (expression.bv_nat 8 8)) undef (mux v_8870 v_8882 (isBitSet v_8867 0)));
      v_8888 <- getRegister of;
      v_8891 <- getRegister af;
      setRegister af (mux v_8870 v_8891 undef);
      setRegister cf v_8885;
      setRegister of (mux (eq v_8864 (expression.bv_nat 8 1)) (notBool_ (eq v_8885 v_8875)) (mux v_8870 v_8888 undef));
      setRegister pf (mux v_8870 v_8877 (parityFlag v_8868));
      setRegister sf (mux v_8870 v_8874 v_8875);
      setRegister zf (mux v_8870 v_8871 (eq v_8868 (expression.bv_nat 8 0)));
      pure ()
    pat_end
