def vfmsub213ps1 : instruction :=
  definst "vfmsub213ps" $ do
    pattern fun (v_2925 : reg (bv 128)) (v_2926 : reg (bv 128)) (v_2927 : reg (bv 128)) => do
      v_5819 <- getRegister v_2926;
      v_5822 <- getRegister v_2927;
      v_5826 <- getRegister v_2925;
      setRegister (lhs.of_reg v_2927) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5819 0 32) 24 8) (MInt2Float (extract v_5822 0 32) 24 8)) (MInt2Float (extract v_5826 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5819 32 64) 24 8) (MInt2Float (extract v_5822 32 64) 24 8)) (MInt2Float (extract v_5826 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5819 64 96) 24 8) (MInt2Float (extract v_5822 64 96) 24 8)) (MInt2Float (extract v_5826 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5819 96 128) 24 8) (MInt2Float (extract v_5822 96 128) 24 8)) (MInt2Float (extract v_5826 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2939 : reg (bv 256)) (v_2940 : reg (bv 256)) (v_2941 : reg (bv 256)) => do
      v_5867 <- getRegister v_2940;
      v_5870 <- getRegister v_2941;
      v_5874 <- getRegister v_2939;
      setRegister (lhs.of_reg v_2941) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 0 32) 24 8) (MInt2Float (extract v_5870 0 32) 24 8)) (MInt2Float (extract v_5874 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 32 64) 24 8) (MInt2Float (extract v_5870 32 64) 24 8)) (MInt2Float (extract v_5874 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 64 96) 24 8) (MInt2Float (extract v_5870 64 96) 24 8)) (MInt2Float (extract v_5874 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 96 128) 24 8) (MInt2Float (extract v_5870 96 128) 24 8)) (MInt2Float (extract v_5874 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 128 160) 24 8) (MInt2Float (extract v_5870 128 160) 24 8)) (MInt2Float (extract v_5874 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 160 192) 24 8) (MInt2Float (extract v_5870 160 192) 24 8)) (MInt2Float (extract v_5874 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 192 224) 24 8) (MInt2Float (extract v_5870 192 224) 24 8)) (MInt2Float (extract v_5874 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5867 224 256) 24 8) (MInt2Float (extract v_5870 224 256) 24 8)) (MInt2Float (extract v_5874 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2922 : Mem) (v_2920 : reg (bv 128)) (v_2921 : reg (bv 128)) => do
      v_11693 <- getRegister v_2920;
      v_11696 <- getRegister v_2921;
      v_11700 <- evaluateAddress v_2922;
      v_11701 <- load v_11700 16;
      setRegister (lhs.of_reg v_2921) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11693 0 32) 24 8) (MInt2Float (extract v_11696 0 32) 24 8)) (MInt2Float (extract v_11701 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11693 32 64) 24 8) (MInt2Float (extract v_11696 32 64) 24 8)) (MInt2Float (extract v_11701 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11693 64 96) 24 8) (MInt2Float (extract v_11696 64 96) 24 8)) (MInt2Float (extract v_11701 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11693 96 128) 24 8) (MInt2Float (extract v_11696 96 128) 24 8)) (MInt2Float (extract v_11701 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2931 : Mem) (v_2934 : reg (bv 256)) (v_2935 : reg (bv 256)) => do
      v_11737 <- getRegister v_2934;
      v_11740 <- getRegister v_2935;
      v_11744 <- evaluateAddress v_2931;
      v_11745 <- load v_11744 32;
      setRegister (lhs.of_reg v_2935) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 0 32) 24 8) (MInt2Float (extract v_11740 0 32) 24 8)) (MInt2Float (extract v_11745 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 32 64) 24 8) (MInt2Float (extract v_11740 32 64) 24 8)) (MInt2Float (extract v_11745 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 64 96) 24 8) (MInt2Float (extract v_11740 64 96) 24 8)) (MInt2Float (extract v_11745 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 96 128) 24 8) (MInt2Float (extract v_11740 96 128) 24 8)) (MInt2Float (extract v_11745 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 128 160) 24 8) (MInt2Float (extract v_11740 128 160) 24 8)) (MInt2Float (extract v_11745 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 160 192) 24 8) (MInt2Float (extract v_11740 160 192) 24 8)) (MInt2Float (extract v_11745 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 192 224) 24 8) (MInt2Float (extract v_11740 192 224) 24 8)) (MInt2Float (extract v_11745 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11737 224 256) 24 8) (MInt2Float (extract v_11740 224 256) 24 8)) (MInt2Float (extract v_11745 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
