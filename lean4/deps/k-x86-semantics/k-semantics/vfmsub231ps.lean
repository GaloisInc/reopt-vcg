def vfmsub231ps1 : instruction :=
  definst "vfmsub231ps" $ do
    pattern fun (v_2967 : reg (bv 128)) (v_2968 : reg (bv 128)) (v_2969 : reg (bv 128)) => do
      v_6044 <- getRegister v_2968;
      v_6047 <- getRegister v_2967;
      v_6051 <- getRegister v_2969;
      setRegister (lhs.of_reg v_2969) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6044 0 32) 24 8) (MInt2Float (extract v_6047 0 32) 24 8)) (MInt2Float (extract v_6051 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6044 32 64) 24 8) (MInt2Float (extract v_6047 32 64) 24 8)) (MInt2Float (extract v_6051 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6044 64 96) 24 8) (MInt2Float (extract v_6047 64 96) 24 8)) (MInt2Float (extract v_6051 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6044 96 128) 24 8) (MInt2Float (extract v_6047 96 128) 24 8)) (MInt2Float (extract v_6051 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2977 : reg (bv 256)) (v_2978 : reg (bv 256)) (v_2979 : reg (bv 256)) => do
      v_6092 <- getRegister v_2978;
      v_6095 <- getRegister v_2977;
      v_6099 <- getRegister v_2979;
      setRegister (lhs.of_reg v_2979) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 0 32) 24 8) (MInt2Float (extract v_6095 0 32) 24 8)) (MInt2Float (extract v_6099 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 32 64) 24 8) (MInt2Float (extract v_6095 32 64) 24 8)) (MInt2Float (extract v_6099 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 64 96) 24 8) (MInt2Float (extract v_6095 64 96) 24 8)) (MInt2Float (extract v_6099 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 96 128) 24 8) (MInt2Float (extract v_6095 96 128) 24 8)) (MInt2Float (extract v_6099 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 128 160) 24 8) (MInt2Float (extract v_6095 128 160) 24 8)) (MInt2Float (extract v_6099 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 160 192) 24 8) (MInt2Float (extract v_6095 160 192) 24 8)) (MInt2Float (extract v_6099 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 192 224) 24 8) (MInt2Float (extract v_6095 192 224) 24 8)) (MInt2Float (extract v_6099 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6092 224 256) 24 8) (MInt2Float (extract v_6095 224 256) 24 8)) (MInt2Float (extract v_6099 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2961 : Mem) (v_2962 : reg (bv 128)) (v_2963 : reg (bv 128)) => do
      v_11892 <- getRegister v_2962;
      v_11895 <- evaluateAddress v_2961;
      v_11896 <- load v_11895 16;
      v_11900 <- getRegister v_2963;
      setRegister (lhs.of_reg v_2963) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11892 0 32) 24 8) (MInt2Float (extract v_11896 0 32) 24 8)) (MInt2Float (extract v_11900 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11892 32 64) 24 8) (MInt2Float (extract v_11896 32 64) 24 8)) (MInt2Float (extract v_11900 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11892 64 96) 24 8) (MInt2Float (extract v_11896 64 96) 24 8)) (MInt2Float (extract v_11900 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11892 96 128) 24 8) (MInt2Float (extract v_11896 96 128) 24 8)) (MInt2Float (extract v_11900 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2972 : Mem) (v_2973 : reg (bv 256)) (v_2974 : reg (bv 256)) => do
      v_11936 <- getRegister v_2973;
      v_11939 <- evaluateAddress v_2972;
      v_11940 <- load v_11939 32;
      v_11944 <- getRegister v_2974;
      setRegister (lhs.of_reg v_2974) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 0 32) 24 8) (MInt2Float (extract v_11940 0 32) 24 8)) (MInt2Float (extract v_11944 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 32 64) 24 8) (MInt2Float (extract v_11940 32 64) 24 8)) (MInt2Float (extract v_11944 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 64 96) 24 8) (MInt2Float (extract v_11940 64 96) 24 8)) (MInt2Float (extract v_11944 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 96 128) 24 8) (MInt2Float (extract v_11940 96 128) 24 8)) (MInt2Float (extract v_11944 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 128 160) 24 8) (MInt2Float (extract v_11940 128 160) 24 8)) (MInt2Float (extract v_11944 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 160 192) 24 8) (MInt2Float (extract v_11940 160 192) 24 8)) (MInt2Float (extract v_11944 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 192 224) 24 8) (MInt2Float (extract v_11940 192 224) 24 8)) (MInt2Float (extract v_11944 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11936 224 256) 24 8) (MInt2Float (extract v_11940 224 256) 24 8)) (MInt2Float (extract v_11944 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
