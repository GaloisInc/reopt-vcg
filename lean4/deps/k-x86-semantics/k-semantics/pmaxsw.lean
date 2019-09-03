def pmaxsw1 : instruction :=
  definst "pmaxsw" $ do
    pattern fun (v_2580 : reg (bv 128)) (v_2581 : reg (bv 128)) => do
      v_4813 <- getRegister v_2581;
      v_4814 <- eval (extract v_4813 0 16);
      v_4815 <- getRegister v_2580;
      v_4816 <- eval (extract v_4815 0 16);
      v_4819 <- eval (extract v_4813 16 32);
      v_4820 <- eval (extract v_4815 16 32);
      v_4823 <- eval (extract v_4813 32 48);
      v_4824 <- eval (extract v_4815 32 48);
      v_4827 <- eval (extract v_4813 48 64);
      v_4828 <- eval (extract v_4815 48 64);
      v_4831 <- eval (extract v_4813 64 80);
      v_4832 <- eval (extract v_4815 64 80);
      v_4835 <- eval (extract v_4813 80 96);
      v_4836 <- eval (extract v_4815 80 96);
      v_4839 <- eval (extract v_4813 96 112);
      v_4840 <- eval (extract v_4815 96 112);
      v_4843 <- eval (extract v_4813 112 128);
      v_4844 <- eval (extract v_4815 112 128);
      setRegister (lhs.of_reg v_2581) (concat (mux (sgt v_4814 v_4816) v_4814 v_4816) (concat (mux (sgt v_4819 v_4820) v_4819 v_4820) (concat (mux (sgt v_4823 v_4824) v_4823 v_4824) (concat (mux (sgt v_4827 v_4828) v_4827 v_4828) (concat (mux (sgt v_4831 v_4832) v_4831 v_4832) (concat (mux (sgt v_4835 v_4836) v_4835 v_4836) (concat (mux (sgt v_4839 v_4840) v_4839 v_4840) (mux (sgt v_4843 v_4844) v_4843 v_4844))))))));
      pure ()
    pat_end;
    pattern fun (v_2576 : Mem) (v_2577 : reg (bv 128)) => do
      v_11884 <- getRegister v_2577;
      v_11885 <- eval (extract v_11884 0 16);
      v_11886 <- evaluateAddress v_2576;
      v_11887 <- load v_11886 16;
      v_11888 <- eval (extract v_11887 0 16);
      v_11891 <- eval (extract v_11884 16 32);
      v_11892 <- eval (extract v_11887 16 32);
      v_11895 <- eval (extract v_11884 32 48);
      v_11896 <- eval (extract v_11887 32 48);
      v_11899 <- eval (extract v_11884 48 64);
      v_11900 <- eval (extract v_11887 48 64);
      v_11903 <- eval (extract v_11884 64 80);
      v_11904 <- eval (extract v_11887 64 80);
      v_11907 <- eval (extract v_11884 80 96);
      v_11908 <- eval (extract v_11887 80 96);
      v_11911 <- eval (extract v_11884 96 112);
      v_11912 <- eval (extract v_11887 96 112);
      v_11915 <- eval (extract v_11884 112 128);
      v_11916 <- eval (extract v_11887 112 128);
      setRegister (lhs.of_reg v_2577) (concat (mux (sgt v_11885 v_11888) v_11885 v_11888) (concat (mux (sgt v_11891 v_11892) v_11891 v_11892) (concat (mux (sgt v_11895 v_11896) v_11895 v_11896) (concat (mux (sgt v_11899 v_11900) v_11899 v_11900) (concat (mux (sgt v_11903 v_11904) v_11903 v_11904) (concat (mux (sgt v_11907 v_11908) v_11907 v_11908) (concat (mux (sgt v_11911 v_11912) v_11911 v_11912) (mux (sgt v_11915 v_11916) v_11915 v_11916))))))));
      pure ()
    pat_end
