def shlq1 : instruction :=
  definst "shlq" $ do
    pattern fun cl (v_2843 : reg (bv 64)) => do
      v_4818 <- getRegister rcx;
      v_4820 <- eval (bv_and (extract v_4818 56 64) (expression.bv_nat 8 63));
      v_4821 <- eval (eq v_4820 (expression.bv_nat 8 0));
      v_4822 <- eval (notBool_ v_4821);
      v_4823 <- getRegister v_2843;
      v_4827 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4823) (concat (expression.bv_nat 57 0) v_4820)) 0 65);
      v_4828 <- eval (extract v_4827 1 65);
      v_4831 <- getRegister zf;
      v_4835 <- eval (isBitSet v_4827 1);
      v_4837 <- getRegister sf;
      v_4844 <- getRegister pf;
      v_4848 <- eval (eq v_4820 (expression.bv_nat 8 1));
      v_4849 <- eval (uge v_4820 (expression.bv_nat 8 64));
      v_4854 <- getRegister cf;
      v_4859 <- eval (bit_or (bit_and v_4849 undef) (bit_and (notBool_ v_4849) (bit_or (bit_and v_4822 (isBitSet v_4827 0)) (bit_and v_4821 (eq v_4854 (expression.bv_nat 1 1))))));
      v_4864 <- eval (bit_and v_4822 undef);
      v_4865 <- getRegister of;
      v_4871 <- getRegister af;
      setRegister (lhs.of_reg v_2843) v_4828;
      setRegister af (bit_or v_4864 (bit_and v_4821 (eq v_4871 (expression.bv_nat 1 1))));
      setRegister cf v_4859;
      setRegister of (bit_or (bit_and v_4848 (notBool_ (eq v_4859 v_4835))) (bit_and (notBool_ v_4848) (bit_or v_4864 (bit_and v_4821 (eq v_4865 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4822 (parityFlag (extract v_4827 57 65))) (bit_and v_4821 (eq v_4844 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4822 v_4835) (bit_and v_4821 (eq v_4837 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4822 (eq v_4828 (expression.bv_nat 64 0))) (bit_and v_4821 (eq v_4831 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2846 : imm int) (v_2848 : reg (bv 64)) => do
      v_4883 <- eval (bv_and (handleImmediateWithSignExtend v_2846 8 8) (expression.bv_nat 8 63));
      v_4884 <- eval (eq v_4883 (expression.bv_nat 8 0));
      v_4885 <- eval (notBool_ v_4884);
      v_4886 <- getRegister v_2848;
      v_4890 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4886) (concat (expression.bv_nat 57 0) v_4883)) 0 65);
      v_4891 <- eval (extract v_4890 1 65);
      v_4894 <- getRegister zf;
      v_4898 <- eval (isBitSet v_4890 1);
      v_4900 <- getRegister sf;
      v_4907 <- getRegister pf;
      v_4911 <- eval (eq v_4883 (expression.bv_nat 8 1));
      v_4912 <- eval (uge v_4883 (expression.bv_nat 8 64));
      v_4917 <- getRegister cf;
      v_4922 <- eval (bit_or (bit_and v_4912 undef) (bit_and (notBool_ v_4912) (bit_or (bit_and v_4885 (isBitSet v_4890 0)) (bit_and v_4884 (eq v_4917 (expression.bv_nat 1 1))))));
      v_4927 <- eval (bit_and v_4885 undef);
      v_4928 <- getRegister of;
      v_4934 <- getRegister af;
      setRegister (lhs.of_reg v_2848) v_4891;
      setRegister af (bit_or v_4927 (bit_and v_4884 (eq v_4934 (expression.bv_nat 1 1))));
      setRegister cf v_4922;
      setRegister of (bit_or (bit_and v_4911 (notBool_ (eq v_4922 v_4898))) (bit_and (notBool_ v_4911) (bit_or v_4927 (bit_and v_4884 (eq v_4928 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4885 (parityFlag (extract v_4890 57 65))) (bit_and v_4884 (eq v_4907 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4885 v_4898) (bit_and v_4884 (eq v_4900 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4885 (eq v_4891 (expression.bv_nat 64 0))) (bit_and v_4884 (eq v_4894 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun cl (v_2832 : Mem) => do
      v_9766 <- evaluateAddress v_2832;
      v_9767 <- load v_9766 8;
      v_9769 <- getRegister rcx;
      v_9771 <- eval (bv_and (extract v_9769 56 64) (expression.bv_nat 8 63));
      v_9774 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9767) (concat (expression.bv_nat 57 0) v_9771)) 0 65);
      v_9775 <- eval (extract v_9774 1 65);
      store v_9766 v_9775 8;
      v_9777 <- eval (eq v_9771 (expression.bv_nat 8 0));
      v_9778 <- eval (notBool_ v_9777);
      v_9781 <- getRegister zf;
      v_9785 <- eval (isBitSet v_9774 1);
      v_9787 <- getRegister sf;
      v_9794 <- getRegister pf;
      v_9798 <- eval (eq v_9771 (expression.bv_nat 8 1));
      v_9799 <- eval (uge v_9771 (expression.bv_nat 8 64));
      v_9804 <- getRegister cf;
      v_9809 <- eval (bit_or (bit_and v_9799 undef) (bit_and (notBool_ v_9799) (bit_or (bit_and v_9778 (isBitSet v_9774 0)) (bit_and v_9777 (eq v_9804 (expression.bv_nat 1 1))))));
      v_9814 <- eval (bit_and v_9778 undef);
      v_9815 <- getRegister of;
      v_9821 <- getRegister af;
      setRegister af (bit_or v_9814 (bit_and v_9777 (eq v_9821 (expression.bv_nat 1 1))));
      setRegister cf v_9809;
      setRegister of (bit_or (bit_and v_9798 (notBool_ (eq v_9809 v_9785))) (bit_and (notBool_ v_9798) (bit_or v_9814 (bit_and v_9777 (eq v_9815 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9778 (parityFlag (extract v_9774 57 65))) (bit_and v_9777 (eq v_9794 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9778 v_9785) (bit_and v_9777 (eq v_9787 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9778 (eq v_9775 (expression.bv_nat 64 0))) (bit_and v_9777 (eq v_9781 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2836 : imm int) (v_2835 : Mem) => do
      v_9831 <- evaluateAddress v_2835;
      v_9832 <- load v_9831 8;
      v_9835 <- eval (bv_and (handleImmediateWithSignExtend v_2836 8 8) (expression.bv_nat 8 63));
      v_9838 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9832) (concat (expression.bv_nat 57 0) v_9835)) 0 65);
      v_9839 <- eval (extract v_9838 1 65);
      store v_9831 v_9839 8;
      v_9841 <- eval (eq v_9835 (expression.bv_nat 8 0));
      v_9842 <- eval (notBool_ v_9841);
      v_9845 <- getRegister zf;
      v_9849 <- eval (isBitSet v_9838 1);
      v_9851 <- getRegister sf;
      v_9858 <- getRegister pf;
      v_9862 <- eval (eq v_9835 (expression.bv_nat 8 1));
      v_9863 <- eval (uge v_9835 (expression.bv_nat 8 64));
      v_9868 <- getRegister cf;
      v_9873 <- eval (bit_or (bit_and v_9863 undef) (bit_and (notBool_ v_9863) (bit_or (bit_and v_9842 (isBitSet v_9838 0)) (bit_and v_9841 (eq v_9868 (expression.bv_nat 1 1))))));
      v_9878 <- eval (bit_and v_9842 undef);
      v_9879 <- getRegister of;
      v_9885 <- getRegister af;
      setRegister af (bit_or v_9878 (bit_and v_9841 (eq v_9885 (expression.bv_nat 1 1))));
      setRegister cf v_9873;
      setRegister of (bit_or (bit_and v_9862 (notBool_ (eq v_9873 v_9849))) (bit_and (notBool_ v_9862) (bit_or v_9878 (bit_and v_9841 (eq v_9879 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9842 (parityFlag (extract v_9838 57 65))) (bit_and v_9841 (eq v_9858 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9842 v_9849) (bit_and v_9841 (eq v_9851 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9842 (eq v_9839 (expression.bv_nat 64 0))) (bit_and v_9841 (eq v_9845 (expression.bv_nat 1 1))));
      pure ()
    pat_end
