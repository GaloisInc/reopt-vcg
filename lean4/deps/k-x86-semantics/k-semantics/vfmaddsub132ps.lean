def vfmaddsub132ps1 : instruction :=
  definst "vfmaddsub132ps" $ do
    pattern fun (v_2703 : reg (bv 128)) (v_2704 : reg (bv 128)) (v_2705 : reg (bv 128)) => do
      v_4901 <- getRegister v_2705;
      v_4904 <- getRegister v_2703;
      v_4908 <- getRegister v_2704;
      setRegister (lhs.of_reg v_2705) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4901 0 32) 24 8) (MInt2Float (extract v_4904 0 32) 24 8)) (MInt2Float (extract v_4908 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4901 32 64) 24 8) (MInt2Float (extract v_4904 32 64) 24 8)) (MInt2Float (extract v_4908 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4901 64 96) 24 8) (MInt2Float (extract v_4904 64 96) 24 8)) (MInt2Float (extract v_4908 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4901 96 128) 24 8) (MInt2Float (extract v_4904 96 128) 24 8)) (MInt2Float (extract v_4908 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2713 : reg (bv 256)) (v_2714 : reg (bv 256)) (v_2715 : reg (bv 256)) => do
      v_4949 <- getRegister v_2715;
      v_4952 <- getRegister v_2713;
      v_4956 <- getRegister v_2714;
      setRegister (lhs.of_reg v_2715) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 0 32) 24 8) (MInt2Float (extract v_4952 0 32) 24 8)) (MInt2Float (extract v_4956 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 32 64) 24 8) (MInt2Float (extract v_4952 32 64) 24 8)) (MInt2Float (extract v_4956 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 64 96) 24 8) (MInt2Float (extract v_4952 64 96) 24 8)) (MInt2Float (extract v_4956 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 96 128) 24 8) (MInt2Float (extract v_4952 96 128) 24 8)) (MInt2Float (extract v_4956 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 128 160) 24 8) (MInt2Float (extract v_4952 128 160) 24 8)) (MInt2Float (extract v_4956 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 160 192) 24 8) (MInt2Float (extract v_4952 160 192) 24 8)) (MInt2Float (extract v_4956 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 192 224) 24 8) (MInt2Float (extract v_4952 192 224) 24 8)) (MInt2Float (extract v_4956 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4949 224 256) 24 8) (MInt2Float (extract v_4952 224 256) 24 8)) (MInt2Float (extract v_4956 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2698 : reg (bv 128)) (v_2699 : reg (bv 128)) => do
      v_10849 <- getRegister v_2699;
      v_10852 <- evaluateAddress v_2697;
      v_10853 <- load v_10852 16;
      v_10857 <- getRegister v_2698;
      setRegister (lhs.of_reg v_2699) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10849 0 32) 24 8) (MInt2Float (extract v_10853 0 32) 24 8)) (MInt2Float (extract v_10857 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10849 32 64) 24 8) (MInt2Float (extract v_10853 32 64) 24 8)) (MInt2Float (extract v_10857 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10849 64 96) 24 8) (MInt2Float (extract v_10853 64 96) 24 8)) (MInt2Float (extract v_10857 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10849 96 128) 24 8) (MInt2Float (extract v_10853 96 128) 24 8)) (MInt2Float (extract v_10857 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2708 : Mem) (v_2709 : reg (bv 256)) (v_2710 : reg (bv 256)) => do
      v_10893 <- getRegister v_2710;
      v_10896 <- evaluateAddress v_2708;
      v_10897 <- load v_10896 32;
      v_10901 <- getRegister v_2709;
      setRegister (lhs.of_reg v_2710) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 0 32) 24 8) (MInt2Float (extract v_10897 0 32) 24 8)) (MInt2Float (extract v_10901 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 32 64) 24 8) (MInt2Float (extract v_10897 32 64) 24 8)) (MInt2Float (extract v_10901 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 64 96) 24 8) (MInt2Float (extract v_10897 64 96) 24 8)) (MInt2Float (extract v_10901 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 96 128) 24 8) (MInt2Float (extract v_10897 96 128) 24 8)) (MInt2Float (extract v_10901 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 128 160) 24 8) (MInt2Float (extract v_10897 128 160) 24 8)) (MInt2Float (extract v_10901 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 160 192) 24 8) (MInt2Float (extract v_10897 160 192) 24 8)) (MInt2Float (extract v_10901 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 192 224) 24 8) (MInt2Float (extract v_10897 192 224) 24 8)) (MInt2Float (extract v_10901 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 224 256) 24 8) (MInt2Float (extract v_10897 224 256) 24 8)) (MInt2Float (extract v_10901 224 256) 24 8)) 32)))));
      pure ()
    pat_end
