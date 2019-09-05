def vshufps1 : instruction :=
  definst "vshufps" $ do
    pattern fun (v_3000 : imm int) (v_2997 : reg (bv 128)) (v_2998 : reg (bv 128)) (v_2999 : reg (bv 128)) => do
      v_6899 <- eval (handleImmediateWithSignExtend v_3000 8 8);
      v_6901 <- eval (isBitSet v_6899 0);
      v_6902 <- getRegister v_2997;
      v_6903 <- eval (extract v_6902 0 32);
      v_6904 <- eval (extract v_6902 64 96);
      v_6906 <- eval (extract v_6902 32 64);
      v_6907 <- eval (extract v_6902 96 128);
      v_6911 <- eval (isBitSet v_6899 2);
      v_6916 <- eval (isBitSet v_6899 4);
      v_6917 <- getRegister v_2998;
      v_6918 <- eval (extract v_6917 0 32);
      v_6919 <- eval (extract v_6917 64 96);
      v_6921 <- eval (extract v_6917 32 64);
      v_6922 <- eval (extract v_6917 96 128);
      v_6926 <- eval (isBitSet v_6899 6);
      setRegister (lhs.of_reg v_2999) (concat (mux (isBitSet v_6899 1) (mux v_6901 v_6903 v_6904) (mux v_6901 v_6906 v_6907)) (concat (mux (isBitSet v_6899 3) (mux v_6911 v_6903 v_6904) (mux v_6911 v_6906 v_6907)) (concat (mux (isBitSet v_6899 5) (mux v_6916 v_6918 v_6919) (mux v_6916 v_6921 v_6922)) (mux (isBitSet v_6899 7) (mux v_6926 v_6918 v_6919) (mux v_6926 v_6921 v_6922)))));
      pure ()
    pat_end;
    pattern fun (v_3013 : imm int) (v_3010 : reg (bv 256)) (v_3011 : reg (bv 256)) (v_3012 : reg (bv 256)) => do
      v_6940 <- eval (handleImmediateWithSignExtend v_3013 8 8);
      v_6941 <- eval (isBitSet v_6940 1);
      v_6942 <- eval (isBitSet v_6940 0);
      v_6943 <- getRegister v_3010;
      v_6944 <- eval (extract v_6943 0 32);
      v_6945 <- eval (extract v_6943 64 96);
      v_6947 <- eval (extract v_6943 32 64);
      v_6948 <- eval (extract v_6943 96 128);
      v_6951 <- eval (isBitSet v_6940 3);
      v_6952 <- eval (isBitSet v_6940 2);
      v_6956 <- eval (isBitSet v_6940 5);
      v_6957 <- eval (isBitSet v_6940 4);
      v_6958 <- getRegister v_3011;
      v_6959 <- eval (extract v_6958 0 32);
      v_6960 <- eval (extract v_6958 64 96);
      v_6962 <- eval (extract v_6958 32 64);
      v_6963 <- eval (extract v_6958 96 128);
      v_6966 <- eval (isBitSet v_6940 7);
      v_6967 <- eval (isBitSet v_6940 6);
      v_6971 <- eval (extract v_6943 128 160);
      v_6972 <- eval (extract v_6943 192 224);
      v_6974 <- eval (extract v_6943 160 192);
      v_6975 <- eval (extract v_6943 224 256);
      v_6981 <- eval (extract v_6958 128 160);
      v_6982 <- eval (extract v_6958 192 224);
      v_6984 <- eval (extract v_6958 160 192);
      v_6985 <- eval (extract v_6958 224 256);
      setRegister (lhs.of_reg v_3012) (concat (mux v_6941 (mux v_6942 v_6944 v_6945) (mux v_6942 v_6947 v_6948)) (concat (mux v_6951 (mux v_6952 v_6944 v_6945) (mux v_6952 v_6947 v_6948)) (concat (mux v_6956 (mux v_6957 v_6959 v_6960) (mux v_6957 v_6962 v_6963)) (concat (mux v_6966 (mux v_6967 v_6959 v_6960) (mux v_6967 v_6962 v_6963)) (concat (mux v_6941 (mux v_6942 v_6971 v_6972) (mux v_6942 v_6974 v_6975)) (concat (mux v_6951 (mux v_6952 v_6971 v_6972) (mux v_6952 v_6974 v_6975)) (concat (mux v_6956 (mux v_6957 v_6981 v_6982) (mux v_6957 v_6984 v_6985)) (mux v_6966 (mux v_6967 v_6981 v_6982) (mux v_6967 v_6984 v_6985)))))))));
      pure ()
    pat_end;
    pattern fun (v_2993 : imm int) (v_2990 : Mem) (v_2991 : reg (bv 128)) (v_2992 : reg (bv 128)) => do
      v_12856 <- eval (handleImmediateWithSignExtend v_2993 8 8);
      v_12858 <- eval (isBitSet v_12856 0);
      v_12859 <- evaluateAddress v_2990;
      v_12860 <- load v_12859 16;
      v_12861 <- eval (extract v_12860 0 32);
      v_12862 <- eval (extract v_12860 64 96);
      v_12864 <- eval (extract v_12860 32 64);
      v_12865 <- eval (extract v_12860 96 128);
      v_12869 <- eval (isBitSet v_12856 2);
      v_12874 <- eval (isBitSet v_12856 4);
      v_12875 <- getRegister v_2991;
      v_12876 <- eval (extract v_12875 0 32);
      v_12877 <- eval (extract v_12875 64 96);
      v_12879 <- eval (extract v_12875 32 64);
      v_12880 <- eval (extract v_12875 96 128);
      v_12884 <- eval (isBitSet v_12856 6);
      setRegister (lhs.of_reg v_2992) (concat (mux (isBitSet v_12856 1) (mux v_12858 v_12861 v_12862) (mux v_12858 v_12864 v_12865)) (concat (mux (isBitSet v_12856 3) (mux v_12869 v_12861 v_12862) (mux v_12869 v_12864 v_12865)) (concat (mux (isBitSet v_12856 5) (mux v_12874 v_12876 v_12877) (mux v_12874 v_12879 v_12880)) (mux (isBitSet v_12856 7) (mux v_12884 v_12876 v_12877) (mux v_12884 v_12879 v_12880)))));
      pure ()
    pat_end;
    pattern fun (v_3006 : imm int) (v_3003 : Mem) (v_3004 : reg (bv 256)) (v_3005 : reg (bv 256)) => do
      v_12892 <- eval (handleImmediateWithSignExtend v_3006 8 8);
      v_12893 <- eval (isBitSet v_12892 1);
      v_12894 <- eval (isBitSet v_12892 0);
      v_12895 <- evaluateAddress v_3003;
      v_12896 <- load v_12895 32;
      v_12897 <- eval (extract v_12896 0 32);
      v_12898 <- eval (extract v_12896 64 96);
      v_12900 <- eval (extract v_12896 32 64);
      v_12901 <- eval (extract v_12896 96 128);
      v_12904 <- eval (isBitSet v_12892 3);
      v_12905 <- eval (isBitSet v_12892 2);
      v_12909 <- eval (isBitSet v_12892 5);
      v_12910 <- eval (isBitSet v_12892 4);
      v_12911 <- getRegister v_3004;
      v_12912 <- eval (extract v_12911 0 32);
      v_12913 <- eval (extract v_12911 64 96);
      v_12915 <- eval (extract v_12911 32 64);
      v_12916 <- eval (extract v_12911 96 128);
      v_12919 <- eval (isBitSet v_12892 7);
      v_12920 <- eval (isBitSet v_12892 6);
      v_12924 <- eval (extract v_12896 128 160);
      v_12925 <- eval (extract v_12896 192 224);
      v_12927 <- eval (extract v_12896 160 192);
      v_12928 <- eval (extract v_12896 224 256);
      v_12934 <- eval (extract v_12911 128 160);
      v_12935 <- eval (extract v_12911 192 224);
      v_12937 <- eval (extract v_12911 160 192);
      v_12938 <- eval (extract v_12911 224 256);
      setRegister (lhs.of_reg v_3005) (concat (mux v_12893 (mux v_12894 v_12897 v_12898) (mux v_12894 v_12900 v_12901)) (concat (mux v_12904 (mux v_12905 v_12897 v_12898) (mux v_12905 v_12900 v_12901)) (concat (mux v_12909 (mux v_12910 v_12912 v_12913) (mux v_12910 v_12915 v_12916)) (concat (mux v_12919 (mux v_12920 v_12912 v_12913) (mux v_12920 v_12915 v_12916)) (concat (mux v_12893 (mux v_12894 v_12924 v_12925) (mux v_12894 v_12927 v_12928)) (concat (mux v_12904 (mux v_12905 v_12924 v_12925) (mux v_12905 v_12927 v_12928)) (concat (mux v_12909 (mux v_12910 v_12934 v_12935) (mux v_12910 v_12937 v_12938)) (mux v_12919 (mux v_12920 v_12934 v_12935) (mux v_12920 v_12937 v_12938)))))))));
      pure ()
    pat_end
