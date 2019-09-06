def vfmaddsub132ps1 : instruction :=
  definst "vfmaddsub132ps" $ do
    pattern fun (v_2727 : reg (bv 128)) (v_2728 : reg (bv 128)) (v_2729 : reg (bv 128)) => do
      v_4928 <- getRegister v_2729;
      v_4931 <- getRegister v_2727;
      v_4935 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2729) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4928 0 32) 24 8) (MInt2Float (extract v_4931 0 32) 24 8)) (MInt2Float (extract v_4935 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4928 32 64) 24 8) (MInt2Float (extract v_4931 32 64) 24 8)) (MInt2Float (extract v_4935 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4928 64 96) 24 8) (MInt2Float (extract v_4931 64 96) 24 8)) (MInt2Float (extract v_4935 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4928 96 128) 24 8) (MInt2Float (extract v_4931 96 128) 24 8)) (MInt2Float (extract v_4935 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2741 : reg (bv 256)) (v_2742 : reg (bv 256)) (v_2743 : reg (bv 256)) => do
      v_4976 <- getRegister v_2743;
      v_4979 <- getRegister v_2741;
      v_4983 <- getRegister v_2742;
      setRegister (lhs.of_reg v_2743) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 0 32) 24 8) (MInt2Float (extract v_4979 0 32) 24 8)) (MInt2Float (extract v_4983 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 32 64) 24 8) (MInt2Float (extract v_4979 32 64) 24 8)) (MInt2Float (extract v_4983 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 64 96) 24 8) (MInt2Float (extract v_4979 64 96) 24 8)) (MInt2Float (extract v_4983 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 96 128) 24 8) (MInt2Float (extract v_4979 96 128) 24 8)) (MInt2Float (extract v_4983 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 128 160) 24 8) (MInt2Float (extract v_4979 128 160) 24 8)) (MInt2Float (extract v_4983 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 160 192) 24 8) (MInt2Float (extract v_4979 160 192) 24 8)) (MInt2Float (extract v_4983 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 192 224) 24 8) (MInt2Float (extract v_4979 192 224) 24 8)) (MInt2Float (extract v_4983 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4976 224 256) 24 8) (MInt2Float (extract v_4979 224 256) 24 8)) (MInt2Float (extract v_4983 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2724 : Mem) (v_2722 : reg (bv 128)) (v_2723 : reg (bv 128)) => do
      v_10876 <- getRegister v_2723;
      v_10879 <- evaluateAddress v_2724;
      v_10880 <- load v_10879 16;
      v_10884 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2723) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10876 0 32) 24 8) (MInt2Float (extract v_10880 0 32) 24 8)) (MInt2Float (extract v_10884 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10876 32 64) 24 8) (MInt2Float (extract v_10880 32 64) 24 8)) (MInt2Float (extract v_10884 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10876 64 96) 24 8) (MInt2Float (extract v_10880 64 96) 24 8)) (MInt2Float (extract v_10884 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10876 96 128) 24 8) (MInt2Float (extract v_10880 96 128) 24 8)) (MInt2Float (extract v_10884 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2733 : Mem) (v_2736 : reg (bv 256)) (v_2737 : reg (bv 256)) => do
      v_10920 <- getRegister v_2737;
      v_10923 <- evaluateAddress v_2733;
      v_10924 <- load v_10923 32;
      v_10928 <- getRegister v_2736;
      setRegister (lhs.of_reg v_2737) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 0 32) 24 8) (MInt2Float (extract v_10924 0 32) 24 8)) (MInt2Float (extract v_10928 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 32 64) 24 8) (MInt2Float (extract v_10924 32 64) 24 8)) (MInt2Float (extract v_10928 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 64 96) 24 8) (MInt2Float (extract v_10924 64 96) 24 8)) (MInt2Float (extract v_10928 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 96 128) 24 8) (MInt2Float (extract v_10924 96 128) 24 8)) (MInt2Float (extract v_10928 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 128 160) 24 8) (MInt2Float (extract v_10924 128 160) 24 8)) (MInt2Float (extract v_10928 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 160 192) 24 8) (MInt2Float (extract v_10924 160 192) 24 8)) (MInt2Float (extract v_10928 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 192 224) 24 8) (MInt2Float (extract v_10924 192 224) 24 8)) (MInt2Float (extract v_10928 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10920 224 256) 24 8) (MInt2Float (extract v_10924 224 256) 24 8)) (MInt2Float (extract v_10928 224 256) 24 8)) 32)))));
      pure ()
    pat_end
