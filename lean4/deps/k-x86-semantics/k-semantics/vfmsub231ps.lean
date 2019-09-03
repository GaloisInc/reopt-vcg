def vfmsub231ps1 : instruction :=
  definst "vfmsub231ps" $ do
    pattern fun (v_2902 : reg (bv 128)) (v_2903 : reg (bv 128)) (v_2904 : reg (bv 128)) => do
      v_5977 <- getRegister v_2903;
      v_5980 <- getRegister v_2902;
      v_5984 <- getRegister v_2904;
      setRegister (lhs.of_reg v_2904) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5977 0 32) 24 8) (MInt2Float (extract v_5980 0 32) 24 8)) (MInt2Float (extract v_5984 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5977 32 64) 24 8) (MInt2Float (extract v_5980 32 64) 24 8)) (MInt2Float (extract v_5984 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5977 64 96) 24 8) (MInt2Float (extract v_5980 64 96) 24 8)) (MInt2Float (extract v_5984 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5977 96 128) 24 8) (MInt2Float (extract v_5980 96 128) 24 8)) (MInt2Float (extract v_5984 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2914 : reg (bv 256)) (v_2915 : reg (bv 256)) (v_2916 : reg (bv 256)) => do
      v_6025 <- getRegister v_2915;
      v_6028 <- getRegister v_2914;
      v_6032 <- getRegister v_2916;
      setRegister (lhs.of_reg v_2916) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 0 32) 24 8) (MInt2Float (extract v_6028 0 32) 24 8)) (MInt2Float (extract v_6032 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 32 64) 24 8) (MInt2Float (extract v_6028 32 64) 24 8)) (MInt2Float (extract v_6032 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 64 96) 24 8) (MInt2Float (extract v_6028 64 96) 24 8)) (MInt2Float (extract v_6032 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 96 128) 24 8) (MInt2Float (extract v_6028 96 128) 24 8)) (MInt2Float (extract v_6032 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 128 160) 24 8) (MInt2Float (extract v_6028 128 160) 24 8)) (MInt2Float (extract v_6032 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 160 192) 24 8) (MInt2Float (extract v_6028 160 192) 24 8)) (MInt2Float (extract v_6032 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 192 224) 24 8) (MInt2Float (extract v_6028 192 224) 24 8)) (MInt2Float (extract v_6032 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6025 224 256) 24 8) (MInt2Float (extract v_6028 224 256) 24 8)) (MInt2Float (extract v_6032 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2899 : Mem) (v_2897 : reg (bv 128)) (v_2898 : reg (bv 128)) => do
      v_11808 <- getRegister v_2897;
      v_11811 <- evaluateAddress v_2899;
      v_11812 <- load v_11811 16;
      v_11816 <- getRegister v_2898;
      setRegister (lhs.of_reg v_2898) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11808 0 32) 24 8) (MInt2Float (extract v_11812 0 32) 24 8)) (MInt2Float (extract v_11816 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11808 32 64) 24 8) (MInt2Float (extract v_11812 32 64) 24 8)) (MInt2Float (extract v_11816 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11808 64 96) 24 8) (MInt2Float (extract v_11812 64 96) 24 8)) (MInt2Float (extract v_11816 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11808 96 128) 24 8) (MInt2Float (extract v_11812 96 128) 24 8)) (MInt2Float (extract v_11816 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2908 : Mem) (v_2909 : reg (bv 256)) (v_2910 : reg (bv 256)) => do
      v_11852 <- getRegister v_2909;
      v_11855 <- evaluateAddress v_2908;
      v_11856 <- load v_11855 32;
      v_11860 <- getRegister v_2910;
      setRegister (lhs.of_reg v_2910) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 0 32) 24 8) (MInt2Float (extract v_11856 0 32) 24 8)) (MInt2Float (extract v_11860 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 32 64) 24 8) (MInt2Float (extract v_11856 32 64) 24 8)) (MInt2Float (extract v_11860 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 64 96) 24 8) (MInt2Float (extract v_11856 64 96) 24 8)) (MInt2Float (extract v_11860 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 96 128) 24 8) (MInt2Float (extract v_11856 96 128) 24 8)) (MInt2Float (extract v_11860 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 128 160) 24 8) (MInt2Float (extract v_11856 128 160) 24 8)) (MInt2Float (extract v_11860 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 160 192) 24 8) (MInt2Float (extract v_11856 160 192) 24 8)) (MInt2Float (extract v_11860 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 192 224) 24 8) (MInt2Float (extract v_11856 192 224) 24 8)) (MInt2Float (extract v_11860 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11852 224 256) 24 8) (MInt2Float (extract v_11856 224 256) 24 8)) (MInt2Float (extract v_11860 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
