def shll1 : instruction :=
  definst "shll" $ do
    pattern fun cl (v_2756 : reg (bv 32)) => do
      v_4750 <- getRegister rcx;
      v_4752 <- eval (bv_and (extract v_4750 56 64) (expression.bv_nat 8 31));
      v_4753 <- eval (uge v_4752 (expression.bv_nat 8 32));
      v_4756 <- eval (eq v_4752 (expression.bv_nat 8 0));
      v_4757 <- eval (notBool_ v_4756);
      v_4758 <- getRegister v_2756;
      v_4759 <- eval (concat (expression.bv_nat 1 0) v_4758);
      v_4764 <- eval (extract (shl v_4759 (uvalueMInt (concat (expression.bv_nat 25 0) v_4752))) 0 (bitwidthMInt v_4759));
      v_4768 <- getRegister cf;
      v_4773 <- eval (bit_or (bit_and v_4753 undef) (bit_and (notBool_ v_4753) (bit_or (bit_and v_4757 (eq (extract v_4764 0 1) (expression.bv_nat 1 1))) (bit_and v_4756 (eq v_4768 (expression.bv_nat 1 1))))));
      v_4776 <- eval (eq (extract v_4764 1 2) (expression.bv_nat 1 1));
      v_4778 <- getRegister sf;
      v_4783 <- eval (extract v_4764 1 33);
      v_4786 <- getRegister zf;
      v_4791 <- eval (bit_and v_4757 undef);
      v_4792 <- getRegister af;
      v_4827 <- getRegister pf;
      v_4832 <- eval (eq v_4752 (expression.bv_nat 8 1));
      v_4837 <- getRegister of;
      setRegister (lhs.of_reg v_2756) v_4783;
      setRegister of (mux (bit_or (bit_and v_4832 (notBool_ (eq v_4773 v_4776))) (bit_and (notBool_ v_4832) (bit_or v_4791 (bit_and v_4756 (eq v_4837 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4757 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4764 32 33) (expression.bv_nat 1 1)) (eq (extract v_4764 31 32) (expression.bv_nat 1 1)))) (eq (extract v_4764 30 31) (expression.bv_nat 1 1)))) (eq (extract v_4764 29 30) (expression.bv_nat 1 1)))) (eq (extract v_4764 28 29) (expression.bv_nat 1 1)))) (eq (extract v_4764 27 28) (expression.bv_nat 1 1)))) (eq (extract v_4764 26 27) (expression.bv_nat 1 1)))) (eq (extract v_4764 25 26) (expression.bv_nat 1 1)))) (bit_and v_4756 (eq v_4827 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4791 (bit_and v_4756 (eq v_4792 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4757 (eq v_4783 (expression.bv_nat 32 0))) (bit_and v_4756 (eq v_4786 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4757 v_4776) (bit_and v_4756 (eq v_4778 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4773 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2759 : imm int) (v_2761 : reg (bv 32)) => do
      v_4852 <- eval (bv_and (handleImmediateWithSignExtend v_2759 8 8) (expression.bv_nat 8 31));
      v_4853 <- eval (uge v_4852 (expression.bv_nat 8 32));
      v_4856 <- eval (eq v_4852 (expression.bv_nat 8 0));
      v_4857 <- eval (notBool_ v_4856);
      v_4858 <- getRegister v_2761;
      v_4859 <- eval (concat (expression.bv_nat 1 0) v_4858);
      v_4864 <- eval (extract (shl v_4859 (uvalueMInt (concat (expression.bv_nat 25 0) v_4852))) 0 (bitwidthMInt v_4859));
      v_4868 <- getRegister cf;
      v_4873 <- eval (bit_or (bit_and v_4853 undef) (bit_and (notBool_ v_4853) (bit_or (bit_and v_4857 (eq (extract v_4864 0 1) (expression.bv_nat 1 1))) (bit_and v_4856 (eq v_4868 (expression.bv_nat 1 1))))));
      v_4876 <- eval (eq (extract v_4864 1 2) (expression.bv_nat 1 1));
      v_4878 <- getRegister sf;
      v_4883 <- eval (extract v_4864 1 33);
      v_4886 <- getRegister zf;
      v_4891 <- eval (bit_and v_4857 undef);
      v_4892 <- getRegister af;
      v_4927 <- getRegister pf;
      v_4932 <- eval (eq v_4852 (expression.bv_nat 8 1));
      v_4937 <- getRegister of;
      setRegister (lhs.of_reg v_2761) v_4883;
      setRegister of (mux (bit_or (bit_and v_4932 (notBool_ (eq v_4873 v_4876))) (bit_and (notBool_ v_4932) (bit_or v_4891 (bit_and v_4856 (eq v_4937 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4857 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4864 32 33) (expression.bv_nat 1 1)) (eq (extract v_4864 31 32) (expression.bv_nat 1 1)))) (eq (extract v_4864 30 31) (expression.bv_nat 1 1)))) (eq (extract v_4864 29 30) (expression.bv_nat 1 1)))) (eq (extract v_4864 28 29) (expression.bv_nat 1 1)))) (eq (extract v_4864 27 28) (expression.bv_nat 1 1)))) (eq (extract v_4864 26 27) (expression.bv_nat 1 1)))) (eq (extract v_4864 25 26) (expression.bv_nat 1 1)))) (bit_and v_4856 (eq v_4927 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4891 (bit_and v_4856 (eq v_4892 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4857 (eq v_4883 (expression.bv_nat 32 0))) (bit_and v_4856 (eq v_4886 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4857 v_4876) (bit_and v_4856 (eq v_4878 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4873 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2765 : reg (bv 32)) => do
      v_4951 <- getRegister v_2765;
      v_4952 <- eval (concat (expression.bv_nat 1 0) v_4951);
      v_4955 <- eval (extract (shl v_4952 1) 0 (bitwidthMInt v_4952));
      v_4956 <- eval (extract v_4955 0 1);
      v_4957 <- eval (extract v_4955 1 2);
      v_4958 <- eval (extract v_4955 1 33);
      setRegister (lhs.of_reg v_2765) v_4958;
      setRegister of (mux (notBool_ (eq (eq v_4956 (expression.bv_nat 1 1)) (eq v_4957 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4955 25 33));
      setRegister af undef;
      setRegister zf (zeroFlag v_4958);
      setRegister sf v_4957;
      setRegister cf v_4956;
      pure ()
    pat_end;
    pattern fun cl (v_2745 : Mem) => do
      v_10872 <- evaluateAddress v_2745;
      v_10873 <- load v_10872 4;
      v_10874 <- eval (concat (expression.bv_nat 1 0) v_10873);
      v_10875 <- getRegister rcx;
      v_10877 <- eval (bv_and (extract v_10875 56 64) (expression.bv_nat 8 31));
      v_10882 <- eval (extract (shl v_10874 (uvalueMInt (concat (expression.bv_nat 25 0) v_10877))) 0 (bitwidthMInt v_10874));
      v_10883 <- eval (extract v_10882 1 33);
      store v_10872 v_10883 4;
      v_10885 <- eval (uge v_10877 (expression.bv_nat 8 32));
      v_10888 <- eval (eq v_10877 (expression.bv_nat 8 0));
      v_10889 <- eval (notBool_ v_10888);
      v_10893 <- getRegister cf;
      v_10898 <- eval (bit_or (bit_and v_10885 undef) (bit_and (notBool_ v_10885) (bit_or (bit_and v_10889 (eq (extract v_10882 0 1) (expression.bv_nat 1 1))) (bit_and v_10888 (eq v_10893 (expression.bv_nat 1 1))))));
      v_10901 <- eval (eq (extract v_10882 1 2) (expression.bv_nat 1 1));
      v_10903 <- getRegister sf;
      v_10910 <- getRegister zf;
      v_10915 <- eval (bit_and v_10889 undef);
      v_10916 <- getRegister af;
      v_10951 <- getRegister pf;
      v_10956 <- eval (eq v_10877 (expression.bv_nat 8 1));
      v_10961 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_10956 (notBool_ (eq v_10898 v_10901))) (bit_and (notBool_ v_10956) (bit_or v_10915 (bit_and v_10888 (eq v_10961 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10889 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10882 32 33) (expression.bv_nat 1 1)) (eq (extract v_10882 31 32) (expression.bv_nat 1 1)))) (eq (extract v_10882 30 31) (expression.bv_nat 1 1)))) (eq (extract v_10882 29 30) (expression.bv_nat 1 1)))) (eq (extract v_10882 28 29) (expression.bv_nat 1 1)))) (eq (extract v_10882 27 28) (expression.bv_nat 1 1)))) (eq (extract v_10882 26 27) (expression.bv_nat 1 1)))) (eq (extract v_10882 25 26) (expression.bv_nat 1 1)))) (bit_and v_10888 (eq v_10951 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_10915 (bit_and v_10888 (eq v_10916 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10889 (eq v_10883 (expression.bv_nat 32 0))) (bit_and v_10888 (eq v_10910 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10889 v_10901) (bit_and v_10888 (eq v_10903 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10898 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2748 : imm int) (v_2749 : Mem) => do
      v_10974 <- evaluateAddress v_2749;
      v_10975 <- load v_10974 4;
      v_10976 <- eval (concat (expression.bv_nat 1 0) v_10975);
      v_10978 <- eval (bv_and (handleImmediateWithSignExtend v_2748 8 8) (expression.bv_nat 8 31));
      v_10983 <- eval (extract (shl v_10976 (uvalueMInt (concat (expression.bv_nat 25 0) v_10978))) 0 (bitwidthMInt v_10976));
      v_10984 <- eval (extract v_10983 1 33);
      store v_10974 v_10984 4;
      v_10986 <- eval (uge v_10978 (expression.bv_nat 8 32));
      v_10989 <- eval (eq v_10978 (expression.bv_nat 8 0));
      v_10990 <- eval (notBool_ v_10989);
      v_10994 <- getRegister cf;
      v_10999 <- eval (bit_or (bit_and v_10986 undef) (bit_and (notBool_ v_10986) (bit_or (bit_and v_10990 (eq (extract v_10983 0 1) (expression.bv_nat 1 1))) (bit_and v_10989 (eq v_10994 (expression.bv_nat 1 1))))));
      v_11002 <- eval (eq (extract v_10983 1 2) (expression.bv_nat 1 1));
      v_11004 <- getRegister sf;
      v_11011 <- getRegister zf;
      v_11016 <- eval (bit_and v_10990 undef);
      v_11017 <- getRegister af;
      v_11052 <- getRegister pf;
      v_11057 <- eval (eq v_10978 (expression.bv_nat 8 1));
      v_11062 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11057 (notBool_ (eq v_10999 v_11002))) (bit_and (notBool_ v_11057) (bit_or v_11016 (bit_and v_10989 (eq v_11062 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10990 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10983 32 33) (expression.bv_nat 1 1)) (eq (extract v_10983 31 32) (expression.bv_nat 1 1)))) (eq (extract v_10983 30 31) (expression.bv_nat 1 1)))) (eq (extract v_10983 29 30) (expression.bv_nat 1 1)))) (eq (extract v_10983 28 29) (expression.bv_nat 1 1)))) (eq (extract v_10983 27 28) (expression.bv_nat 1 1)))) (eq (extract v_10983 26 27) (expression.bv_nat 1 1)))) (eq (extract v_10983 25 26) (expression.bv_nat 1 1)))) (bit_and v_10989 (eq v_11052 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11016 (bit_and v_10989 (eq v_11017 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10990 (eq v_10984 (expression.bv_nat 32 0))) (bit_and v_10989 (eq v_11011 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10990 v_11002) (bit_and v_10989 (eq v_11004 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10999 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
