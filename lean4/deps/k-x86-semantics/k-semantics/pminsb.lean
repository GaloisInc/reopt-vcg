def pminsb1 : instruction :=
  definst "pminsb" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) => do
      v_5075 <- getRegister v_2694;
      v_5076 <- eval (extract v_5075 0 8);
      v_5077 <- getRegister v_2693;
      v_5078 <- eval (extract v_5077 0 8);
      v_5081 <- eval (extract v_5075 8 16);
      v_5082 <- eval (extract v_5077 8 16);
      v_5085 <- eval (extract v_5075 16 24);
      v_5086 <- eval (extract v_5077 16 24);
      v_5089 <- eval (extract v_5075 24 32);
      v_5090 <- eval (extract v_5077 24 32);
      v_5093 <- eval (extract v_5075 32 40);
      v_5094 <- eval (extract v_5077 32 40);
      v_5097 <- eval (extract v_5075 40 48);
      v_5098 <- eval (extract v_5077 40 48);
      v_5101 <- eval (extract v_5075 48 56);
      v_5102 <- eval (extract v_5077 48 56);
      v_5105 <- eval (extract v_5075 56 64);
      v_5106 <- eval (extract v_5077 56 64);
      v_5109 <- eval (extract v_5075 64 72);
      v_5110 <- eval (extract v_5077 64 72);
      v_5113 <- eval (extract v_5075 72 80);
      v_5114 <- eval (extract v_5077 72 80);
      v_5117 <- eval (extract v_5075 80 88);
      v_5118 <- eval (extract v_5077 80 88);
      v_5121 <- eval (extract v_5075 88 96);
      v_5122 <- eval (extract v_5077 88 96);
      v_5125 <- eval (extract v_5075 96 104);
      v_5126 <- eval (extract v_5077 96 104);
      v_5129 <- eval (extract v_5075 104 112);
      v_5130 <- eval (extract v_5077 104 112);
      v_5133 <- eval (extract v_5075 112 120);
      v_5134 <- eval (extract v_5077 112 120);
      v_5137 <- eval (extract v_5075 120 128);
      v_5138 <- eval (extract v_5077 120 128);
      setRegister (lhs.of_reg v_2694) (concat (mux (slt v_5076 v_5078) v_5076 v_5078) (concat (mux (slt v_5081 v_5082) v_5081 v_5082) (concat (mux (slt v_5085 v_5086) v_5085 v_5086) (concat (mux (slt v_5089 v_5090) v_5089 v_5090) (concat (mux (slt v_5093 v_5094) v_5093 v_5094) (concat (mux (slt v_5097 v_5098) v_5097 v_5098) (concat (mux (slt v_5101 v_5102) v_5101 v_5102) (concat (mux (slt v_5105 v_5106) v_5105 v_5106) (concat (mux (slt v_5109 v_5110) v_5109 v_5110) (concat (mux (slt v_5113 v_5114) v_5113 v_5114) (concat (mux (slt v_5117 v_5118) v_5117 v_5118) (concat (mux (slt v_5121 v_5122) v_5121 v_5122) (concat (mux (slt v_5125 v_5126) v_5125 v_5126) (concat (mux (slt v_5129 v_5130) v_5129 v_5130) (concat (mux (slt v_5133 v_5134) v_5133 v_5134) (mux (slt v_5137 v_5138) v_5137 v_5138))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2689 : Mem) (v_2690 : reg (bv 128)) => do
      v_11910 <- getRegister v_2690;
      v_11911 <- eval (extract v_11910 0 8);
      v_11912 <- evaluateAddress v_2689;
      v_11913 <- load v_11912 16;
      v_11914 <- eval (extract v_11913 0 8);
      v_11917 <- eval (extract v_11910 8 16);
      v_11918 <- eval (extract v_11913 8 16);
      v_11921 <- eval (extract v_11910 16 24);
      v_11922 <- eval (extract v_11913 16 24);
      v_11925 <- eval (extract v_11910 24 32);
      v_11926 <- eval (extract v_11913 24 32);
      v_11929 <- eval (extract v_11910 32 40);
      v_11930 <- eval (extract v_11913 32 40);
      v_11933 <- eval (extract v_11910 40 48);
      v_11934 <- eval (extract v_11913 40 48);
      v_11937 <- eval (extract v_11910 48 56);
      v_11938 <- eval (extract v_11913 48 56);
      v_11941 <- eval (extract v_11910 56 64);
      v_11942 <- eval (extract v_11913 56 64);
      v_11945 <- eval (extract v_11910 64 72);
      v_11946 <- eval (extract v_11913 64 72);
      v_11949 <- eval (extract v_11910 72 80);
      v_11950 <- eval (extract v_11913 72 80);
      v_11953 <- eval (extract v_11910 80 88);
      v_11954 <- eval (extract v_11913 80 88);
      v_11957 <- eval (extract v_11910 88 96);
      v_11958 <- eval (extract v_11913 88 96);
      v_11961 <- eval (extract v_11910 96 104);
      v_11962 <- eval (extract v_11913 96 104);
      v_11965 <- eval (extract v_11910 104 112);
      v_11966 <- eval (extract v_11913 104 112);
      v_11969 <- eval (extract v_11910 112 120);
      v_11970 <- eval (extract v_11913 112 120);
      v_11973 <- eval (extract v_11910 120 128);
      v_11974 <- eval (extract v_11913 120 128);
      setRegister (lhs.of_reg v_2690) (concat (mux (slt v_11911 v_11914) v_11911 v_11914) (concat (mux (slt v_11917 v_11918) v_11917 v_11918) (concat (mux (slt v_11921 v_11922) v_11921 v_11922) (concat (mux (slt v_11925 v_11926) v_11925 v_11926) (concat (mux (slt v_11929 v_11930) v_11929 v_11930) (concat (mux (slt v_11933 v_11934) v_11933 v_11934) (concat (mux (slt v_11937 v_11938) v_11937 v_11938) (concat (mux (slt v_11941 v_11942) v_11941 v_11942) (concat (mux (slt v_11945 v_11946) v_11945 v_11946) (concat (mux (slt v_11949 v_11950) v_11949 v_11950) (concat (mux (slt v_11953 v_11954) v_11953 v_11954) (concat (mux (slt v_11957 v_11958) v_11957 v_11958) (concat (mux (slt v_11961 v_11962) v_11961 v_11962) (concat (mux (slt v_11965 v_11966) v_11965 v_11966) (concat (mux (slt v_11969 v_11970) v_11969 v_11970) (mux (slt v_11973 v_11974) v_11973 v_11974))))))))))))))));
      pure ()
    pat_end
