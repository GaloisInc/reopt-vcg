def pmaxuw1 : instruction :=
  definst "pmaxuw" $ do
    pattern fun (v_2684 : reg (bv 128)) (v_2685 : reg (bv 128)) => do
      v_5029 <- getRegister v_2685;
      v_5030 <- eval (extract v_5029 0 16);
      v_5031 <- getRegister v_2684;
      v_5032 <- eval (extract v_5031 0 16);
      v_5035 <- eval (extract v_5029 16 32);
      v_5036 <- eval (extract v_5031 16 32);
      v_5039 <- eval (extract v_5029 32 48);
      v_5040 <- eval (extract v_5031 32 48);
      v_5043 <- eval (extract v_5029 48 64);
      v_5044 <- eval (extract v_5031 48 64);
      v_5047 <- eval (extract v_5029 64 80);
      v_5048 <- eval (extract v_5031 64 80);
      v_5051 <- eval (extract v_5029 80 96);
      v_5052 <- eval (extract v_5031 80 96);
      v_5055 <- eval (extract v_5029 96 112);
      v_5056 <- eval (extract v_5031 96 112);
      v_5059 <- eval (extract v_5029 112 128);
      v_5060 <- eval (extract v_5031 112 128);
      setRegister (lhs.of_reg v_2685) (concat (mux (ugt v_5030 v_5032) v_5030 v_5032) (concat (mux (ugt v_5035 v_5036) v_5035 v_5036) (concat (mux (ugt v_5039 v_5040) v_5039 v_5040) (concat (mux (ugt v_5043 v_5044) v_5043 v_5044) (concat (mux (ugt v_5047 v_5048) v_5047 v_5048) (concat (mux (ugt v_5051 v_5052) v_5051 v_5052) (concat (mux (ugt v_5055 v_5056) v_5055 v_5056) (mux (ugt v_5059 v_5060) v_5059 v_5060))))))));
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) (v_2681 : reg (bv 128)) => do
      v_11867 <- getRegister v_2681;
      v_11868 <- eval (extract v_11867 0 16);
      v_11869 <- evaluateAddress v_2680;
      v_11870 <- load v_11869 16;
      v_11871 <- eval (extract v_11870 0 16);
      v_11874 <- eval (extract v_11867 16 32);
      v_11875 <- eval (extract v_11870 16 32);
      v_11878 <- eval (extract v_11867 32 48);
      v_11879 <- eval (extract v_11870 32 48);
      v_11882 <- eval (extract v_11867 48 64);
      v_11883 <- eval (extract v_11870 48 64);
      v_11886 <- eval (extract v_11867 64 80);
      v_11887 <- eval (extract v_11870 64 80);
      v_11890 <- eval (extract v_11867 80 96);
      v_11891 <- eval (extract v_11870 80 96);
      v_11894 <- eval (extract v_11867 96 112);
      v_11895 <- eval (extract v_11870 96 112);
      v_11898 <- eval (extract v_11867 112 128);
      v_11899 <- eval (extract v_11870 112 128);
      setRegister (lhs.of_reg v_2681) (concat (mux (ugt v_11868 v_11871) v_11868 v_11871) (concat (mux (ugt v_11874 v_11875) v_11874 v_11875) (concat (mux (ugt v_11878 v_11879) v_11878 v_11879) (concat (mux (ugt v_11882 v_11883) v_11882 v_11883) (concat (mux (ugt v_11886 v_11887) v_11886 v_11887) (concat (mux (ugt v_11890 v_11891) v_11890 v_11891) (concat (mux (ugt v_11894 v_11895) v_11894 v_11895) (mux (ugt v_11898 v_11899) v_11898 v_11899))))))));
      pure ()
    pat_end
