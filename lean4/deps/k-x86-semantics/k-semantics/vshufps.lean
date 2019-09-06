def vshufps1 : instruction :=
  definst "vshufps" $ do
    pattern fun (v_3023 : imm int) (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) (v_3027 : reg (bv 128)) => do
      v_6926 <- eval (handleImmediateWithSignExtend v_3023 8 8);
      v_6928 <- eval (isBitSet v_6926 0);
      v_6929 <- getRegister v_3025;
      v_6930 <- eval (extract v_6929 0 32);
      v_6931 <- eval (extract v_6929 64 96);
      v_6933 <- eval (extract v_6929 32 64);
      v_6934 <- eval (extract v_6929 96 128);
      v_6938 <- eval (isBitSet v_6926 2);
      v_6943 <- eval (isBitSet v_6926 4);
      v_6944 <- getRegister v_3026;
      v_6945 <- eval (extract v_6944 0 32);
      v_6946 <- eval (extract v_6944 64 96);
      v_6948 <- eval (extract v_6944 32 64);
      v_6949 <- eval (extract v_6944 96 128);
      v_6953 <- eval (isBitSet v_6926 6);
      setRegister (lhs.of_reg v_3027) (concat (mux (isBitSet v_6926 1) (mux v_6928 v_6930 v_6931) (mux v_6928 v_6933 v_6934)) (concat (mux (isBitSet v_6926 3) (mux v_6938 v_6930 v_6931) (mux v_6938 v_6933 v_6934)) (concat (mux (isBitSet v_6926 5) (mux v_6943 v_6945 v_6946) (mux v_6943 v_6948 v_6949)) (mux (isBitSet v_6926 7) (mux v_6953 v_6945 v_6946) (mux v_6953 v_6948 v_6949)))));
      pure ()
    pat_end;
    pattern fun (v_3036 : imm int) (v_3038 : reg (bv 256)) (v_3039 : reg (bv 256)) (v_3040 : reg (bv 256)) => do
      v_6967 <- eval (handleImmediateWithSignExtend v_3036 8 8);
      v_6968 <- eval (isBitSet v_6967 1);
      v_6969 <- eval (isBitSet v_6967 0);
      v_6970 <- getRegister v_3038;
      v_6971 <- eval (extract v_6970 0 32);
      v_6972 <- eval (extract v_6970 64 96);
      v_6974 <- eval (extract v_6970 32 64);
      v_6975 <- eval (extract v_6970 96 128);
      v_6978 <- eval (isBitSet v_6967 3);
      v_6979 <- eval (isBitSet v_6967 2);
      v_6983 <- eval (isBitSet v_6967 5);
      v_6984 <- eval (isBitSet v_6967 4);
      v_6985 <- getRegister v_3039;
      v_6986 <- eval (extract v_6985 0 32);
      v_6987 <- eval (extract v_6985 64 96);
      v_6989 <- eval (extract v_6985 32 64);
      v_6990 <- eval (extract v_6985 96 128);
      v_6993 <- eval (isBitSet v_6967 7);
      v_6994 <- eval (isBitSet v_6967 6);
      v_6998 <- eval (extract v_6970 128 160);
      v_6999 <- eval (extract v_6970 192 224);
      v_7001 <- eval (extract v_6970 160 192);
      v_7002 <- eval (extract v_6970 224 256);
      v_7008 <- eval (extract v_6985 128 160);
      v_7009 <- eval (extract v_6985 192 224);
      v_7011 <- eval (extract v_6985 160 192);
      v_7012 <- eval (extract v_6985 224 256);
      setRegister (lhs.of_reg v_3040) (concat (mux v_6968 (mux v_6969 v_6971 v_6972) (mux v_6969 v_6974 v_6975)) (concat (mux v_6978 (mux v_6979 v_6971 v_6972) (mux v_6979 v_6974 v_6975)) (concat (mux v_6983 (mux v_6984 v_6986 v_6987) (mux v_6984 v_6989 v_6990)) (concat (mux v_6993 (mux v_6994 v_6986 v_6987) (mux v_6994 v_6989 v_6990)) (concat (mux v_6968 (mux v_6969 v_6998 v_6999) (mux v_6969 v_7001 v_7002)) (concat (mux v_6978 (mux v_6979 v_6998 v_6999) (mux v_6979 v_7001 v_7002)) (concat (mux v_6983 (mux v_6984 v_7008 v_7009) (mux v_6984 v_7011 v_7012)) (mux v_6993 (mux v_6994 v_7008 v_7009) (mux v_6994 v_7011 v_7012)))))))));
      pure ()
    pat_end;
    pattern fun (v_3017 : imm int) (v_3018 : Mem) (v_3019 : reg (bv 128)) (v_3020 : reg (bv 128)) => do
      v_12883 <- eval (handleImmediateWithSignExtend v_3017 8 8);
      v_12885 <- eval (isBitSet v_12883 0);
      v_12886 <- evaluateAddress v_3018;
      v_12887 <- load v_12886 16;
      v_12888 <- eval (extract v_12887 0 32);
      v_12889 <- eval (extract v_12887 64 96);
      v_12891 <- eval (extract v_12887 32 64);
      v_12892 <- eval (extract v_12887 96 128);
      v_12896 <- eval (isBitSet v_12883 2);
      v_12901 <- eval (isBitSet v_12883 4);
      v_12902 <- getRegister v_3019;
      v_12903 <- eval (extract v_12902 0 32);
      v_12904 <- eval (extract v_12902 64 96);
      v_12906 <- eval (extract v_12902 32 64);
      v_12907 <- eval (extract v_12902 96 128);
      v_12911 <- eval (isBitSet v_12883 6);
      setRegister (lhs.of_reg v_3020) (concat (mux (isBitSet v_12883 1) (mux v_12885 v_12888 v_12889) (mux v_12885 v_12891 v_12892)) (concat (mux (isBitSet v_12883 3) (mux v_12896 v_12888 v_12889) (mux v_12896 v_12891 v_12892)) (concat (mux (isBitSet v_12883 5) (mux v_12901 v_12903 v_12904) (mux v_12901 v_12906 v_12907)) (mux (isBitSet v_12883 7) (mux v_12911 v_12903 v_12904) (mux v_12911 v_12906 v_12907)))));
      pure ()
    pat_end;
    pattern fun (v_3030 : imm int) (v_3031 : Mem) (v_3032 : reg (bv 256)) (v_3033 : reg (bv 256)) => do
      v_12919 <- eval (handleImmediateWithSignExtend v_3030 8 8);
      v_12920 <- eval (isBitSet v_12919 1);
      v_12921 <- eval (isBitSet v_12919 0);
      v_12922 <- evaluateAddress v_3031;
      v_12923 <- load v_12922 32;
      v_12924 <- eval (extract v_12923 0 32);
      v_12925 <- eval (extract v_12923 64 96);
      v_12927 <- eval (extract v_12923 32 64);
      v_12928 <- eval (extract v_12923 96 128);
      v_12931 <- eval (isBitSet v_12919 3);
      v_12932 <- eval (isBitSet v_12919 2);
      v_12936 <- eval (isBitSet v_12919 5);
      v_12937 <- eval (isBitSet v_12919 4);
      v_12938 <- getRegister v_3032;
      v_12939 <- eval (extract v_12938 0 32);
      v_12940 <- eval (extract v_12938 64 96);
      v_12942 <- eval (extract v_12938 32 64);
      v_12943 <- eval (extract v_12938 96 128);
      v_12946 <- eval (isBitSet v_12919 7);
      v_12947 <- eval (isBitSet v_12919 6);
      v_12951 <- eval (extract v_12923 128 160);
      v_12952 <- eval (extract v_12923 192 224);
      v_12954 <- eval (extract v_12923 160 192);
      v_12955 <- eval (extract v_12923 224 256);
      v_12961 <- eval (extract v_12938 128 160);
      v_12962 <- eval (extract v_12938 192 224);
      v_12964 <- eval (extract v_12938 160 192);
      v_12965 <- eval (extract v_12938 224 256);
      setRegister (lhs.of_reg v_3033) (concat (mux v_12920 (mux v_12921 v_12924 v_12925) (mux v_12921 v_12927 v_12928)) (concat (mux v_12931 (mux v_12932 v_12924 v_12925) (mux v_12932 v_12927 v_12928)) (concat (mux v_12936 (mux v_12937 v_12939 v_12940) (mux v_12937 v_12942 v_12943)) (concat (mux v_12946 (mux v_12947 v_12939 v_12940) (mux v_12947 v_12942 v_12943)) (concat (mux v_12920 (mux v_12921 v_12951 v_12952) (mux v_12921 v_12954 v_12955)) (concat (mux v_12931 (mux v_12932 v_12951 v_12952) (mux v_12932 v_12954 v_12955)) (concat (mux v_12936 (mux v_12937 v_12961 v_12962) (mux v_12937 v_12964 v_12965)) (mux v_12946 (mux v_12947 v_12961 v_12962) (mux v_12947 v_12964 v_12965)))))))));
      pure ()
    pat_end
