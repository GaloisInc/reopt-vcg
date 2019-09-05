def sarq1 : instruction :=
  definst "sarq" $ do
    pattern fun cl (v_3150 : reg (bv 64)) => do
      v_6814 <- getRegister rcx;
      v_6816 <- eval (bv_and (extract v_6814 56 64) (expression.bv_nat 8 63));
      v_6817 <- eval (eq v_6816 (expression.bv_nat 8 0));
      v_6818 <- eval (notBool_ v_6817);
      v_6819 <- getRegister v_3150;
      v_6822 <- eval (ashr (concat v_6819 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_6816));
      v_6823 <- eval (extract v_6822 0 64);
      v_6826 <- getRegister zf;
      v_6832 <- getRegister sf;
      v_6839 <- getRegister pf;
      v_6845 <- eval (bit_and v_6818 undef);
      v_6846 <- getRegister of;
      v_6853 <- getRegister cf;
      v_6857 <- getRegister af;
      setRegister (lhs.of_reg v_3150) v_6823;
      setRegister af (bit_or v_6845 (bit_and v_6817 (eq v_6857 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6818 (isBitSet v_6822 64)) (bit_and v_6817 (eq v_6853 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6816 (expression.bv_nat 8 1))) (bit_or v_6845 (bit_and v_6817 (eq v_6846 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6818 (parityFlag (extract v_6822 56 64))) (bit_and v_6817 (eq v_6839 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6818 (isBitSet v_6822 0)) (bit_and v_6817 (eq v_6832 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6818 (eq v_6823 (expression.bv_nat 64 0))) (bit_and v_6817 (eq v_6826 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3153 : imm int) (v_3155 : reg (bv 64)) => do
      v_6869 <- eval (bv_and (handleImmediateWithSignExtend v_3153 8 8) (expression.bv_nat 8 63));
      v_6870 <- eval (eq v_6869 (expression.bv_nat 8 0));
      v_6871 <- eval (notBool_ v_6870);
      v_6872 <- getRegister v_3155;
      v_6875 <- eval (ashr (concat v_6872 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_6869));
      v_6876 <- eval (extract v_6875 0 64);
      v_6879 <- getRegister zf;
      v_6885 <- getRegister sf;
      v_6892 <- getRegister pf;
      v_6898 <- eval (bit_and v_6871 undef);
      v_6899 <- getRegister of;
      v_6906 <- getRegister cf;
      v_6910 <- getRegister af;
      setRegister (lhs.of_reg v_3155) v_6876;
      setRegister af (bit_or v_6898 (bit_and v_6870 (eq v_6910 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6871 (isBitSet v_6875 64)) (bit_and v_6870 (eq v_6906 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6869 (expression.bv_nat 8 1))) (bit_or v_6898 (bit_and v_6870 (eq v_6899 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6871 (parityFlag (extract v_6875 56 64))) (bit_and v_6870 (eq v_6892 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6871 (isBitSet v_6875 0)) (bit_and v_6870 (eq v_6885 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6871 (eq v_6876 (expression.bv_nat 64 0))) (bit_and v_6870 (eq v_6879 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3158 : reg (bv 64)) => do
      v_8513 <- getRegister v_3158;
      v_8515 <- eval (ashr (concat v_8513 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_8516 <- eval (extract v_8515 0 64);
      setRegister (lhs.of_reg v_3158) v_8516;
      setRegister af undef;
      setRegister cf (isBitSet v_8515 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8515 56 64));
      setRegister sf (isBitSet v_8515 0);
      setRegister zf (zeroFlag v_8516);
      pure ()
    pat_end;
    pattern fun cl (v_3136 : Mem) => do
      v_13839 <- evaluateAddress v_3136;
      v_13840 <- load v_13839 8;
      v_13842 <- getRegister rcx;
      v_13844 <- eval (bv_and (extract v_13842 56 64) (expression.bv_nat 8 63));
      v_13846 <- eval (ashr (concat v_13840 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_13844));
      v_13847 <- eval (extract v_13846 0 64);
      store v_13839 v_13847 8;
      v_13849 <- eval (eq v_13844 (expression.bv_nat 8 0));
      v_13850 <- eval (notBool_ v_13849);
      v_13853 <- getRegister zf;
      v_13859 <- getRegister sf;
      v_13866 <- getRegister pf;
      v_13872 <- eval (bit_and v_13850 undef);
      v_13873 <- getRegister of;
      v_13880 <- getRegister cf;
      v_13884 <- getRegister af;
      setRegister af (bit_or v_13872 (bit_and v_13849 (eq v_13884 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13850 (isBitSet v_13846 64)) (bit_and v_13849 (eq v_13880 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13844 (expression.bv_nat 8 1))) (bit_or v_13872 (bit_and v_13849 (eq v_13873 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13850 (parityFlag (extract v_13846 56 64))) (bit_and v_13849 (eq v_13866 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13850 (isBitSet v_13846 0)) (bit_and v_13849 (eq v_13859 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13850 (eq v_13847 (expression.bv_nat 64 0))) (bit_and v_13849 (eq v_13853 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3139 : imm int) (v_3140 : Mem) => do
      v_13894 <- evaluateAddress v_3140;
      v_13895 <- load v_13894 8;
      v_13898 <- eval (bv_and (handleImmediateWithSignExtend v_3139 8 8) (expression.bv_nat 8 63));
      v_13900 <- eval (ashr (concat v_13895 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_13898));
      v_13901 <- eval (extract v_13900 0 64);
      store v_13894 v_13901 8;
      v_13903 <- eval (eq v_13898 (expression.bv_nat 8 0));
      v_13904 <- eval (notBool_ v_13903);
      v_13907 <- getRegister zf;
      v_13913 <- getRegister sf;
      v_13920 <- getRegister pf;
      v_13926 <- eval (bit_and v_13904 undef);
      v_13927 <- getRegister of;
      v_13934 <- getRegister cf;
      v_13938 <- getRegister af;
      setRegister af (bit_or v_13926 (bit_and v_13903 (eq v_13938 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13904 (isBitSet v_13900 64)) (bit_and v_13903 (eq v_13934 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13898 (expression.bv_nat 8 1))) (bit_or v_13926 (bit_and v_13903 (eq v_13927 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13904 (parityFlag (extract v_13900 56 64))) (bit_and v_13903 (eq v_13920 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13904 (isBitSet v_13900 0)) (bit_and v_13903 (eq v_13913 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13904 (eq v_13901 (expression.bv_nat 64 0))) (bit_and v_13903 (eq v_13907 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3143 : Mem) => do
      v_14603 <- evaluateAddress v_3143;
      v_14604 <- load v_14603 8;
      v_14606 <- eval (ashr (concat v_14604 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_14607 <- eval (extract v_14606 0 64);
      store v_14603 v_14607 8;
      setRegister af undef;
      setRegister cf (isBitSet v_14606 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_14606 56 64));
      setRegister sf (isBitSet v_14606 0);
      setRegister zf (zeroFlag v_14607);
      pure ()
    pat_end
