def pmaxub1 : instruction :=
  definst "pmaxub" $ do
    pattern fun (v_2589 : reg (bv 128)) (v_2590 : reg (bv 128)) => do
      v_4859 <- getRegister v_2590;
      v_4860 <- eval (extract v_4859 0 8);
      v_4861 <- getRegister v_2589;
      v_4862 <- eval (extract v_4861 0 8);
      v_4865 <- eval (extract v_4859 8 16);
      v_4866 <- eval (extract v_4861 8 16);
      v_4869 <- eval (extract v_4859 16 24);
      v_4870 <- eval (extract v_4861 16 24);
      v_4873 <- eval (extract v_4859 24 32);
      v_4874 <- eval (extract v_4861 24 32);
      v_4877 <- eval (extract v_4859 32 40);
      v_4878 <- eval (extract v_4861 32 40);
      v_4881 <- eval (extract v_4859 40 48);
      v_4882 <- eval (extract v_4861 40 48);
      v_4885 <- eval (extract v_4859 48 56);
      v_4886 <- eval (extract v_4861 48 56);
      v_4889 <- eval (extract v_4859 56 64);
      v_4890 <- eval (extract v_4861 56 64);
      v_4893 <- eval (extract v_4859 64 72);
      v_4894 <- eval (extract v_4861 64 72);
      v_4897 <- eval (extract v_4859 72 80);
      v_4898 <- eval (extract v_4861 72 80);
      v_4901 <- eval (extract v_4859 80 88);
      v_4902 <- eval (extract v_4861 80 88);
      v_4905 <- eval (extract v_4859 88 96);
      v_4906 <- eval (extract v_4861 88 96);
      v_4909 <- eval (extract v_4859 96 104);
      v_4910 <- eval (extract v_4861 96 104);
      v_4913 <- eval (extract v_4859 104 112);
      v_4914 <- eval (extract v_4861 104 112);
      v_4917 <- eval (extract v_4859 112 120);
      v_4918 <- eval (extract v_4861 112 120);
      v_4921 <- eval (extract v_4859 120 128);
      v_4922 <- eval (extract v_4861 120 128);
      setRegister (lhs.of_reg v_2590) (concat (mux (ugt v_4860 v_4862) v_4860 v_4862) (concat (mux (ugt v_4865 v_4866) v_4865 v_4866) (concat (mux (ugt v_4869 v_4870) v_4869 v_4870) (concat (mux (ugt v_4873 v_4874) v_4873 v_4874) (concat (mux (ugt v_4877 v_4878) v_4877 v_4878) (concat (mux (ugt v_4881 v_4882) v_4881 v_4882) (concat (mux (ugt v_4885 v_4886) v_4885 v_4886) (concat (mux (ugt v_4889 v_4890) v_4889 v_4890) (concat (mux (ugt v_4893 v_4894) v_4893 v_4894) (concat (mux (ugt v_4897 v_4898) v_4897 v_4898) (concat (mux (ugt v_4901 v_4902) v_4901 v_4902) (concat (mux (ugt v_4905 v_4906) v_4905 v_4906) (concat (mux (ugt v_4909 v_4910) v_4909 v_4910) (concat (mux (ugt v_4913 v_4914) v_4913 v_4914) (concat (mux (ugt v_4917 v_4918) v_4917 v_4918) (mux (ugt v_4921 v_4922) v_4921 v_4922))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2585 : Mem) (v_2586 : reg (bv 128)) => do
      v_11927 <- getRegister v_2586;
      v_11928 <- eval (extract v_11927 0 8);
      v_11929 <- evaluateAddress v_2585;
      v_11930 <- load v_11929 16;
      v_11931 <- eval (extract v_11930 0 8);
      v_11934 <- eval (extract v_11927 8 16);
      v_11935 <- eval (extract v_11930 8 16);
      v_11938 <- eval (extract v_11927 16 24);
      v_11939 <- eval (extract v_11930 16 24);
      v_11942 <- eval (extract v_11927 24 32);
      v_11943 <- eval (extract v_11930 24 32);
      v_11946 <- eval (extract v_11927 32 40);
      v_11947 <- eval (extract v_11930 32 40);
      v_11950 <- eval (extract v_11927 40 48);
      v_11951 <- eval (extract v_11930 40 48);
      v_11954 <- eval (extract v_11927 48 56);
      v_11955 <- eval (extract v_11930 48 56);
      v_11958 <- eval (extract v_11927 56 64);
      v_11959 <- eval (extract v_11930 56 64);
      v_11962 <- eval (extract v_11927 64 72);
      v_11963 <- eval (extract v_11930 64 72);
      v_11966 <- eval (extract v_11927 72 80);
      v_11967 <- eval (extract v_11930 72 80);
      v_11970 <- eval (extract v_11927 80 88);
      v_11971 <- eval (extract v_11930 80 88);
      v_11974 <- eval (extract v_11927 88 96);
      v_11975 <- eval (extract v_11930 88 96);
      v_11978 <- eval (extract v_11927 96 104);
      v_11979 <- eval (extract v_11930 96 104);
      v_11982 <- eval (extract v_11927 104 112);
      v_11983 <- eval (extract v_11930 104 112);
      v_11986 <- eval (extract v_11927 112 120);
      v_11987 <- eval (extract v_11930 112 120);
      v_11990 <- eval (extract v_11927 120 128);
      v_11991 <- eval (extract v_11930 120 128);
      setRegister (lhs.of_reg v_2586) (concat (mux (ugt v_11928 v_11931) v_11928 v_11931) (concat (mux (ugt v_11934 v_11935) v_11934 v_11935) (concat (mux (ugt v_11938 v_11939) v_11938 v_11939) (concat (mux (ugt v_11942 v_11943) v_11942 v_11943) (concat (mux (ugt v_11946 v_11947) v_11946 v_11947) (concat (mux (ugt v_11950 v_11951) v_11950 v_11951) (concat (mux (ugt v_11954 v_11955) v_11954 v_11955) (concat (mux (ugt v_11958 v_11959) v_11958 v_11959) (concat (mux (ugt v_11962 v_11963) v_11962 v_11963) (concat (mux (ugt v_11966 v_11967) v_11966 v_11967) (concat (mux (ugt v_11970 v_11971) v_11970 v_11971) (concat (mux (ugt v_11974 v_11975) v_11974 v_11975) (concat (mux (ugt v_11978 v_11979) v_11978 v_11979) (concat (mux (ugt v_11982 v_11983) v_11982 v_11983) (concat (mux (ugt v_11986 v_11987) v_11986 v_11987) (mux (ugt v_11990 v_11991) v_11990 v_11991))))))))))))))));
      pure ()
    pat_end
