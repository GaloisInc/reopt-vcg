def pmaxub1 : instruction :=
  definst "pmaxub" $ do
    pattern fun (v_2638 : reg (bv 128)) (v_2639 : reg (bv 128)) => do
      v_4890 <- getRegister v_2639;
      v_4891 <- eval (extract v_4890 0 8);
      v_4892 <- getRegister v_2638;
      v_4893 <- eval (extract v_4892 0 8);
      v_4896 <- eval (extract v_4890 8 16);
      v_4897 <- eval (extract v_4892 8 16);
      v_4900 <- eval (extract v_4890 16 24);
      v_4901 <- eval (extract v_4892 16 24);
      v_4904 <- eval (extract v_4890 24 32);
      v_4905 <- eval (extract v_4892 24 32);
      v_4908 <- eval (extract v_4890 32 40);
      v_4909 <- eval (extract v_4892 32 40);
      v_4912 <- eval (extract v_4890 40 48);
      v_4913 <- eval (extract v_4892 40 48);
      v_4916 <- eval (extract v_4890 48 56);
      v_4917 <- eval (extract v_4892 48 56);
      v_4920 <- eval (extract v_4890 56 64);
      v_4921 <- eval (extract v_4892 56 64);
      v_4924 <- eval (extract v_4890 64 72);
      v_4925 <- eval (extract v_4892 64 72);
      v_4928 <- eval (extract v_4890 72 80);
      v_4929 <- eval (extract v_4892 72 80);
      v_4932 <- eval (extract v_4890 80 88);
      v_4933 <- eval (extract v_4892 80 88);
      v_4936 <- eval (extract v_4890 88 96);
      v_4937 <- eval (extract v_4892 88 96);
      v_4940 <- eval (extract v_4890 96 104);
      v_4941 <- eval (extract v_4892 96 104);
      v_4944 <- eval (extract v_4890 104 112);
      v_4945 <- eval (extract v_4892 104 112);
      v_4948 <- eval (extract v_4890 112 120);
      v_4949 <- eval (extract v_4892 112 120);
      v_4952 <- eval (extract v_4890 120 128);
      v_4953 <- eval (extract v_4892 120 128);
      setRegister (lhs.of_reg v_2639) (concat (mux (ugt v_4891 v_4893) v_4891 v_4893) (concat (mux (ugt v_4896 v_4897) v_4896 v_4897) (concat (mux (ugt v_4900 v_4901) v_4900 v_4901) (concat (mux (ugt v_4904 v_4905) v_4904 v_4905) (concat (mux (ugt v_4908 v_4909) v_4908 v_4909) (concat (mux (ugt v_4912 v_4913) v_4912 v_4913) (concat (mux (ugt v_4916 v_4917) v_4916 v_4917) (concat (mux (ugt v_4920 v_4921) v_4920 v_4921) (concat (mux (ugt v_4924 v_4925) v_4924 v_4925) (concat (mux (ugt v_4928 v_4929) v_4928 v_4929) (concat (mux (ugt v_4932 v_4933) v_4932 v_4933) (concat (mux (ugt v_4936 v_4937) v_4936 v_4937) (concat (mux (ugt v_4940 v_4941) v_4940 v_4941) (concat (mux (ugt v_4944 v_4945) v_4944 v_4945) (concat (mux (ugt v_4948 v_4949) v_4948 v_4949) (mux (ugt v_4952 v_4953) v_4952 v_4953))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2635 : Mem) (v_2634 : reg (bv 128)) => do
      v_11785 <- getRegister v_2634;
      v_11786 <- eval (extract v_11785 0 8);
      v_11787 <- evaluateAddress v_2635;
      v_11788 <- load v_11787 16;
      v_11789 <- eval (extract v_11788 0 8);
      v_11792 <- eval (extract v_11785 8 16);
      v_11793 <- eval (extract v_11788 8 16);
      v_11796 <- eval (extract v_11785 16 24);
      v_11797 <- eval (extract v_11788 16 24);
      v_11800 <- eval (extract v_11785 24 32);
      v_11801 <- eval (extract v_11788 24 32);
      v_11804 <- eval (extract v_11785 32 40);
      v_11805 <- eval (extract v_11788 32 40);
      v_11808 <- eval (extract v_11785 40 48);
      v_11809 <- eval (extract v_11788 40 48);
      v_11812 <- eval (extract v_11785 48 56);
      v_11813 <- eval (extract v_11788 48 56);
      v_11816 <- eval (extract v_11785 56 64);
      v_11817 <- eval (extract v_11788 56 64);
      v_11820 <- eval (extract v_11785 64 72);
      v_11821 <- eval (extract v_11788 64 72);
      v_11824 <- eval (extract v_11785 72 80);
      v_11825 <- eval (extract v_11788 72 80);
      v_11828 <- eval (extract v_11785 80 88);
      v_11829 <- eval (extract v_11788 80 88);
      v_11832 <- eval (extract v_11785 88 96);
      v_11833 <- eval (extract v_11788 88 96);
      v_11836 <- eval (extract v_11785 96 104);
      v_11837 <- eval (extract v_11788 96 104);
      v_11840 <- eval (extract v_11785 104 112);
      v_11841 <- eval (extract v_11788 104 112);
      v_11844 <- eval (extract v_11785 112 120);
      v_11845 <- eval (extract v_11788 112 120);
      v_11848 <- eval (extract v_11785 120 128);
      v_11849 <- eval (extract v_11788 120 128);
      setRegister (lhs.of_reg v_2634) (concat (mux (ugt v_11786 v_11789) v_11786 v_11789) (concat (mux (ugt v_11792 v_11793) v_11792 v_11793) (concat (mux (ugt v_11796 v_11797) v_11796 v_11797) (concat (mux (ugt v_11800 v_11801) v_11800 v_11801) (concat (mux (ugt v_11804 v_11805) v_11804 v_11805) (concat (mux (ugt v_11808 v_11809) v_11808 v_11809) (concat (mux (ugt v_11812 v_11813) v_11812 v_11813) (concat (mux (ugt v_11816 v_11817) v_11816 v_11817) (concat (mux (ugt v_11820 v_11821) v_11820 v_11821) (concat (mux (ugt v_11824 v_11825) v_11824 v_11825) (concat (mux (ugt v_11828 v_11829) v_11828 v_11829) (concat (mux (ugt v_11832 v_11833) v_11832 v_11833) (concat (mux (ugt v_11836 v_11837) v_11836 v_11837) (concat (mux (ugt v_11840 v_11841) v_11840 v_11841) (concat (mux (ugt v_11844 v_11845) v_11844 v_11845) (mux (ugt v_11848 v_11849) v_11848 v_11849))))))))))))))));
      pure ()
    pat_end
