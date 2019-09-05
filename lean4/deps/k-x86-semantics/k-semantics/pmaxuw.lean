def pmaxuw1 : instruction :=
  definst "pmaxuw" $ do
    pattern fun (v_2656 : reg (bv 128)) (v_2657 : reg (bv 128)) => do
      v_5002 <- getRegister v_2657;
      v_5003 <- eval (extract v_5002 0 16);
      v_5004 <- getRegister v_2656;
      v_5005 <- eval (extract v_5004 0 16);
      v_5008 <- eval (extract v_5002 16 32);
      v_5009 <- eval (extract v_5004 16 32);
      v_5012 <- eval (extract v_5002 32 48);
      v_5013 <- eval (extract v_5004 32 48);
      v_5016 <- eval (extract v_5002 48 64);
      v_5017 <- eval (extract v_5004 48 64);
      v_5020 <- eval (extract v_5002 64 80);
      v_5021 <- eval (extract v_5004 64 80);
      v_5024 <- eval (extract v_5002 80 96);
      v_5025 <- eval (extract v_5004 80 96);
      v_5028 <- eval (extract v_5002 96 112);
      v_5029 <- eval (extract v_5004 96 112);
      v_5032 <- eval (extract v_5002 112 128);
      v_5033 <- eval (extract v_5004 112 128);
      setRegister (lhs.of_reg v_2657) (concat (mux (ugt v_5003 v_5005) v_5003 v_5005) (concat (mux (ugt v_5008 v_5009) v_5008 v_5009) (concat (mux (ugt v_5012 v_5013) v_5012 v_5013) (concat (mux (ugt v_5016 v_5017) v_5016 v_5017) (concat (mux (ugt v_5020 v_5021) v_5020 v_5021) (concat (mux (ugt v_5024 v_5025) v_5024 v_5025) (concat (mux (ugt v_5028 v_5029) v_5028 v_5029) (mux (ugt v_5032 v_5033) v_5032 v_5033))))))));
      pure ()
    pat_end;
    pattern fun (v_2653 : Mem) (v_2652 : reg (bv 128)) => do
      v_11891 <- getRegister v_2652;
      v_11892 <- eval (extract v_11891 0 16);
      v_11893 <- evaluateAddress v_2653;
      v_11894 <- load v_11893 16;
      v_11895 <- eval (extract v_11894 0 16);
      v_11898 <- eval (extract v_11891 16 32);
      v_11899 <- eval (extract v_11894 16 32);
      v_11902 <- eval (extract v_11891 32 48);
      v_11903 <- eval (extract v_11894 32 48);
      v_11906 <- eval (extract v_11891 48 64);
      v_11907 <- eval (extract v_11894 48 64);
      v_11910 <- eval (extract v_11891 64 80);
      v_11911 <- eval (extract v_11894 64 80);
      v_11914 <- eval (extract v_11891 80 96);
      v_11915 <- eval (extract v_11894 80 96);
      v_11918 <- eval (extract v_11891 96 112);
      v_11919 <- eval (extract v_11894 96 112);
      v_11922 <- eval (extract v_11891 112 128);
      v_11923 <- eval (extract v_11894 112 128);
      setRegister (lhs.of_reg v_2652) (concat (mux (ugt v_11892 v_11895) v_11892 v_11895) (concat (mux (ugt v_11898 v_11899) v_11898 v_11899) (concat (mux (ugt v_11902 v_11903) v_11902 v_11903) (concat (mux (ugt v_11906 v_11907) v_11906 v_11907) (concat (mux (ugt v_11910 v_11911) v_11910 v_11911) (concat (mux (ugt v_11914 v_11915) v_11914 v_11915) (concat (mux (ugt v_11918 v_11919) v_11918 v_11919) (mux (ugt v_11922 v_11923) v_11922 v_11923))))))));
      pure ()
    pat_end
