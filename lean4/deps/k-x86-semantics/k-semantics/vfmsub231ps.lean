def vfmsub231ps1 : instruction :=
  definst "vfmsub231ps" $ do
    pattern fun (v_2991 : reg (bv 128)) (v_2992 : reg (bv 128)) (v_2993 : reg (bv 128)) => do
      v_6071 <- getRegister v_2992;
      v_6074 <- getRegister v_2991;
      v_6078 <- getRegister v_2993;
      setRegister (lhs.of_reg v_2993) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6071 0 32) 24 8) (MInt2Float (extract v_6074 0 32) 24 8)) (MInt2Float (extract v_6078 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6071 32 64) 24 8) (MInt2Float (extract v_6074 32 64) 24 8)) (MInt2Float (extract v_6078 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6071 64 96) 24 8) (MInt2Float (extract v_6074 64 96) 24 8)) (MInt2Float (extract v_6078 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6071 96 128) 24 8) (MInt2Float (extract v_6074 96 128) 24 8)) (MInt2Float (extract v_6078 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3005 : reg (bv 256)) (v_3006 : reg (bv 256)) (v_3007 : reg (bv 256)) => do
      v_6119 <- getRegister v_3006;
      v_6122 <- getRegister v_3005;
      v_6126 <- getRegister v_3007;
      setRegister (lhs.of_reg v_3007) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 0 32) 24 8) (MInt2Float (extract v_6122 0 32) 24 8)) (MInt2Float (extract v_6126 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 32 64) 24 8) (MInt2Float (extract v_6122 32 64) 24 8)) (MInt2Float (extract v_6126 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 64 96) 24 8) (MInt2Float (extract v_6122 64 96) 24 8)) (MInt2Float (extract v_6126 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 96 128) 24 8) (MInt2Float (extract v_6122 96 128) 24 8)) (MInt2Float (extract v_6126 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 128 160) 24 8) (MInt2Float (extract v_6122 128 160) 24 8)) (MInt2Float (extract v_6126 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 160 192) 24 8) (MInt2Float (extract v_6122 160 192) 24 8)) (MInt2Float (extract v_6126 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 192 224) 24 8) (MInt2Float (extract v_6122 192 224) 24 8)) (MInt2Float (extract v_6126 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6119 224 256) 24 8) (MInt2Float (extract v_6122 224 256) 24 8)) (MInt2Float (extract v_6126 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2988 : Mem) (v_2986 : reg (bv 128)) (v_2987 : reg (bv 128)) => do
      v_11919 <- getRegister v_2986;
      v_11922 <- evaluateAddress v_2988;
      v_11923 <- load v_11922 16;
      v_11927 <- getRegister v_2987;
      setRegister (lhs.of_reg v_2987) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11919 0 32) 24 8) (MInt2Float (extract v_11923 0 32) 24 8)) (MInt2Float (extract v_11927 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11919 32 64) 24 8) (MInt2Float (extract v_11923 32 64) 24 8)) (MInt2Float (extract v_11927 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11919 64 96) 24 8) (MInt2Float (extract v_11923 64 96) 24 8)) (MInt2Float (extract v_11927 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11919 96 128) 24 8) (MInt2Float (extract v_11923 96 128) 24 8)) (MInt2Float (extract v_11927 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2997 : Mem) (v_3000 : reg (bv 256)) (v_3001 : reg (bv 256)) => do
      v_11963 <- getRegister v_3000;
      v_11966 <- evaluateAddress v_2997;
      v_11967 <- load v_11966 32;
      v_11971 <- getRegister v_3001;
      setRegister (lhs.of_reg v_3001) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 0 32) 24 8) (MInt2Float (extract v_11967 0 32) 24 8)) (MInt2Float (extract v_11971 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 32 64) 24 8) (MInt2Float (extract v_11967 32 64) 24 8)) (MInt2Float (extract v_11971 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 64 96) 24 8) (MInt2Float (extract v_11967 64 96) 24 8)) (MInt2Float (extract v_11971 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 96 128) 24 8) (MInt2Float (extract v_11967 96 128) 24 8)) (MInt2Float (extract v_11971 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 128 160) 24 8) (MInt2Float (extract v_11967 128 160) 24 8)) (MInt2Float (extract v_11971 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 160 192) 24 8) (MInt2Float (extract v_11967 160 192) 24 8)) (MInt2Float (extract v_11971 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 192 224) 24 8) (MInt2Float (extract v_11967 192 224) 24 8)) (MInt2Float (extract v_11971 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11963 224 256) 24 8) (MInt2Float (extract v_11967 224 256) 24 8)) (MInt2Float (extract v_11971 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
