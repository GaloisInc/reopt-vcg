def vfmsub213ps1 : instruction :=
  definst "vfmsub213ps" $ do
    pattern fun (v_2849 : reg (bv 128)) (v_2850 : reg (bv 128)) (v_2851 : reg (bv 128)) => do
      v_7969 <- getRegister v_2850;
      v_7970 <- eval (extract v_7969 0 32);
      v_7978 <- getRegister v_2851;
      v_7979 <- eval (extract v_7978 0 32);
      v_7988 <- getRegister v_2849;
      v_7989 <- eval (extract v_7988 0 32);
      v_7999 <- eval (extract v_7969 32 64);
      v_8007 <- eval (extract v_7978 32 64);
      v_8016 <- eval (extract v_7988 32 64);
      v_8026 <- eval (extract v_7969 64 96);
      v_8034 <- eval (extract v_7978 64 96);
      v_8043 <- eval (extract v_7988 64 96);
      v_8053 <- eval (extract v_7969 96 128);
      v_8061 <- eval (extract v_7978 96 128);
      v_8070 <- eval (extract v_7988 96 128);
      setRegister (lhs.of_reg v_2851) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7970 0 1)) (uvalueMInt (extract v_7970 1 9)) (uvalueMInt (extract v_7970 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7979 0 1)) (uvalueMInt (extract v_7979 1 9)) (uvalueMInt (extract v_7979 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7989 0 1)) (uvalueMInt (extract v_7989 1 9)) (uvalueMInt (extract v_7989 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7999 0 1)) (uvalueMInt (extract v_7999 1 9)) (uvalueMInt (extract v_7999 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8007 0 1)) (uvalueMInt (extract v_8007 1 9)) (uvalueMInt (extract v_8007 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8016 0 1)) (uvalueMInt (extract v_8016 1 9)) (uvalueMInt (extract v_8016 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8026 0 1)) (uvalueMInt (extract v_8026 1 9)) (uvalueMInt (extract v_8026 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8034 0 1)) (uvalueMInt (extract v_8034 1 9)) (uvalueMInt (extract v_8034 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8043 0 1)) (uvalueMInt (extract v_8043 1 9)) (uvalueMInt (extract v_8043 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8053 0 1)) (uvalueMInt (extract v_8053 1 9)) (uvalueMInt (extract v_8053 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8061 0 1)) (uvalueMInt (extract v_8061 1 9)) (uvalueMInt (extract v_8061 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8070 0 1)) (uvalueMInt (extract v_8070 1 9)) (uvalueMInt (extract v_8070 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2860 : reg (bv 256)) (v_2861 : reg (bv 256)) (v_2862 : reg (bv 256)) => do
      v_8089 <- getRegister v_2861;
      v_8090 <- eval (extract v_8089 0 32);
      v_8098 <- getRegister v_2862;
      v_8099 <- eval (extract v_8098 0 32);
      v_8108 <- getRegister v_2860;
      v_8109 <- eval (extract v_8108 0 32);
      v_8119 <- eval (extract v_8089 32 64);
      v_8127 <- eval (extract v_8098 32 64);
      v_8136 <- eval (extract v_8108 32 64);
      v_8147 <- eval (extract v_8089 64 96);
      v_8155 <- eval (extract v_8098 64 96);
      v_8164 <- eval (extract v_8108 64 96);
      v_8174 <- eval (extract v_8089 96 128);
      v_8182 <- eval (extract v_8098 96 128);
      v_8191 <- eval (extract v_8108 96 128);
      v_8201 <- eval (extract v_8089 128 160);
      v_8209 <- eval (extract v_8098 128 160);
      v_8218 <- eval (extract v_8108 128 160);
      v_8228 <- eval (extract v_8089 160 192);
      v_8236 <- eval (extract v_8098 160 192);
      v_8245 <- eval (extract v_8108 160 192);
      v_8255 <- eval (extract v_8089 192 224);
      v_8263 <- eval (extract v_8098 192 224);
      v_8272 <- eval (extract v_8108 192 224);
      v_8282 <- eval (extract v_8089 224 256);
      v_8290 <- eval (extract v_8098 224 256);
      v_8299 <- eval (extract v_8108 224 256);
      setRegister (lhs.of_reg v_2862) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8090 0 1)) (uvalueMInt (extract v_8090 1 9)) (uvalueMInt (extract v_8090 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8099 0 1)) (uvalueMInt (extract v_8099 1 9)) (uvalueMInt (extract v_8099 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8109 0 1)) (uvalueMInt (extract v_8109 1 9)) (uvalueMInt (extract v_8109 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8119 0 1)) (uvalueMInt (extract v_8119 1 9)) (uvalueMInt (extract v_8119 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8127 0 1)) (uvalueMInt (extract v_8127 1 9)) (uvalueMInt (extract v_8127 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8136 0 1)) (uvalueMInt (extract v_8136 1 9)) (uvalueMInt (extract v_8136 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8147 0 1)) (uvalueMInt (extract v_8147 1 9)) (uvalueMInt (extract v_8147 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8155 0 1)) (uvalueMInt (extract v_8155 1 9)) (uvalueMInt (extract v_8155 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8164 0 1)) (uvalueMInt (extract v_8164 1 9)) (uvalueMInt (extract v_8164 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8174 0 1)) (uvalueMInt (extract v_8174 1 9)) (uvalueMInt (extract v_8174 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8182 0 1)) (uvalueMInt (extract v_8182 1 9)) (uvalueMInt (extract v_8182 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8191 0 1)) (uvalueMInt (extract v_8191 1 9)) (uvalueMInt (extract v_8191 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8201 0 1)) (uvalueMInt (extract v_8201 1 9)) (uvalueMInt (extract v_8201 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8209 0 1)) (uvalueMInt (extract v_8209 1 9)) (uvalueMInt (extract v_8209 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8218 0 1)) (uvalueMInt (extract v_8218 1 9)) (uvalueMInt (extract v_8218 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8228 0 1)) (uvalueMInt (extract v_8228 1 9)) (uvalueMInt (extract v_8228 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8236 0 1)) (uvalueMInt (extract v_8236 1 9)) (uvalueMInt (extract v_8236 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8245 0 1)) (uvalueMInt (extract v_8245 1 9)) (uvalueMInt (extract v_8245 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8255 0 1)) (uvalueMInt (extract v_8255 1 9)) (uvalueMInt (extract v_8255 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8263 0 1)) (uvalueMInt (extract v_8263 1 9)) (uvalueMInt (extract v_8263 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8272 0 1)) (uvalueMInt (extract v_8272 1 9)) (uvalueMInt (extract v_8272 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8282 0 1)) (uvalueMInt (extract v_8282 1 9)) (uvalueMInt (extract v_8282 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8290 0 1)) (uvalueMInt (extract v_8290 1 9)) (uvalueMInt (extract v_8290 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8299 0 1)) (uvalueMInt (extract v_8299 1 9)) (uvalueMInt (extract v_8299 9 32)))) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) (v_2844 : reg (bv 128)) (v_2845 : reg (bv 128)) => do
      v_18758 <- getRegister v_2844;
      v_18759 <- eval (extract v_18758 0 32);
      v_18767 <- getRegister v_2845;
      v_18768 <- eval (extract v_18767 0 32);
      v_18777 <- evaluateAddress v_2846;
      v_18778 <- load v_18777 16;
      v_18779 <- eval (extract v_18778 0 32);
      v_18789 <- eval (extract v_18758 32 64);
      v_18797 <- eval (extract v_18767 32 64);
      v_18806 <- eval (extract v_18778 32 64);
      v_18816 <- eval (extract v_18758 64 96);
      v_18824 <- eval (extract v_18767 64 96);
      v_18833 <- eval (extract v_18778 64 96);
      v_18843 <- eval (extract v_18758 96 128);
      v_18851 <- eval (extract v_18767 96 128);
      v_18860 <- eval (extract v_18778 96 128);
      setRegister (lhs.of_reg v_2845) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18759 0 1)) (uvalueMInt (extract v_18759 1 9)) (uvalueMInt (extract v_18759 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18768 0 1)) (uvalueMInt (extract v_18768 1 9)) (uvalueMInt (extract v_18768 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18779 0 1)) (uvalueMInt (extract v_18779 1 9)) (uvalueMInt (extract v_18779 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18789 0 1)) (uvalueMInt (extract v_18789 1 9)) (uvalueMInt (extract v_18789 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18797 0 1)) (uvalueMInt (extract v_18797 1 9)) (uvalueMInt (extract v_18797 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18806 0 1)) (uvalueMInt (extract v_18806 1 9)) (uvalueMInt (extract v_18806 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18816 0 1)) (uvalueMInt (extract v_18816 1 9)) (uvalueMInt (extract v_18816 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18824 0 1)) (uvalueMInt (extract v_18824 1 9)) (uvalueMInt (extract v_18824 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18833 0 1)) (uvalueMInt (extract v_18833 1 9)) (uvalueMInt (extract v_18833 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18843 0 1)) (uvalueMInt (extract v_18843 1 9)) (uvalueMInt (extract v_18843 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18851 0 1)) (uvalueMInt (extract v_18851 1 9)) (uvalueMInt (extract v_18851 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18860 0 1)) (uvalueMInt (extract v_18860 1 9)) (uvalueMInt (extract v_18860 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2855 : Mem) (v_2856 : reg (bv 256)) (v_2857 : reg (bv 256)) => do
      v_18874 <- getRegister v_2856;
      v_18875 <- eval (extract v_18874 0 32);
      v_18883 <- getRegister v_2857;
      v_18884 <- eval (extract v_18883 0 32);
      v_18893 <- evaluateAddress v_2855;
      v_18894 <- load v_18893 32;
      v_18895 <- eval (extract v_18894 0 32);
      v_18905 <- eval (extract v_18874 32 64);
      v_18913 <- eval (extract v_18883 32 64);
      v_18922 <- eval (extract v_18894 32 64);
      v_18933 <- eval (extract v_18874 64 96);
      v_18941 <- eval (extract v_18883 64 96);
      v_18950 <- eval (extract v_18894 64 96);
      v_18960 <- eval (extract v_18874 96 128);
      v_18968 <- eval (extract v_18883 96 128);
      v_18977 <- eval (extract v_18894 96 128);
      v_18987 <- eval (extract v_18874 128 160);
      v_18995 <- eval (extract v_18883 128 160);
      v_19004 <- eval (extract v_18894 128 160);
      v_19014 <- eval (extract v_18874 160 192);
      v_19022 <- eval (extract v_18883 160 192);
      v_19031 <- eval (extract v_18894 160 192);
      v_19041 <- eval (extract v_18874 192 224);
      v_19049 <- eval (extract v_18883 192 224);
      v_19058 <- eval (extract v_18894 192 224);
      v_19068 <- eval (extract v_18874 224 256);
      v_19076 <- eval (extract v_18883 224 256);
      v_19085 <- eval (extract v_18894 224 256);
      setRegister (lhs.of_reg v_2857) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18875 0 1)) (uvalueMInt (extract v_18875 1 9)) (uvalueMInt (extract v_18875 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18884 0 1)) (uvalueMInt (extract v_18884 1 9)) (uvalueMInt (extract v_18884 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18895 0 1)) (uvalueMInt (extract v_18895 1 9)) (uvalueMInt (extract v_18895 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18905 0 1)) (uvalueMInt (extract v_18905 1 9)) (uvalueMInt (extract v_18905 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18913 0 1)) (uvalueMInt (extract v_18913 1 9)) (uvalueMInt (extract v_18913 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18922 0 1)) (uvalueMInt (extract v_18922 1 9)) (uvalueMInt (extract v_18922 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18933 0 1)) (uvalueMInt (extract v_18933 1 9)) (uvalueMInt (extract v_18933 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18941 0 1)) (uvalueMInt (extract v_18941 1 9)) (uvalueMInt (extract v_18941 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18950 0 1)) (uvalueMInt (extract v_18950 1 9)) (uvalueMInt (extract v_18950 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18960 0 1)) (uvalueMInt (extract v_18960 1 9)) (uvalueMInt (extract v_18960 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18968 0 1)) (uvalueMInt (extract v_18968 1 9)) (uvalueMInt (extract v_18968 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18977 0 1)) (uvalueMInt (extract v_18977 1 9)) (uvalueMInt (extract v_18977 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18987 0 1)) (uvalueMInt (extract v_18987 1 9)) (uvalueMInt (extract v_18987 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18995 0 1)) (uvalueMInt (extract v_18995 1 9)) (uvalueMInt (extract v_18995 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19004 0 1)) (uvalueMInt (extract v_19004 1 9)) (uvalueMInt (extract v_19004 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19014 0 1)) (uvalueMInt (extract v_19014 1 9)) (uvalueMInt (extract v_19014 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19022 0 1)) (uvalueMInt (extract v_19022 1 9)) (uvalueMInt (extract v_19022 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19031 0 1)) (uvalueMInt (extract v_19031 1 9)) (uvalueMInt (extract v_19031 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19041 0 1)) (uvalueMInt (extract v_19041 1 9)) (uvalueMInt (extract v_19041 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19049 0 1)) (uvalueMInt (extract v_19049 1 9)) (uvalueMInt (extract v_19049 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19058 0 1)) (uvalueMInt (extract v_19058 1 9)) (uvalueMInt (extract v_19058 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19068 0 1)) (uvalueMInt (extract v_19068 1 9)) (uvalueMInt (extract v_19068 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19076 0 1)) (uvalueMInt (extract v_19076 1 9)) (uvalueMInt (extract v_19076 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19085 0 1)) (uvalueMInt (extract v_19085 1 9)) (uvalueMInt (extract v_19085 9 32)))) 32)))))));
      pure ()
    pat_end
