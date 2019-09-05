def vfmaddsub213ps1 : instruction :=
  definst "vfmaddsub213ps" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) (v_2749 : reg (bv 128)) => do
      v_5113 <- getRegister v_2748;
      v_5116 <- getRegister v_2749;
      v_5120 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2749) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5113 0 32) 24 8) (MInt2Float (extract v_5116 0 32) 24 8)) (MInt2Float (extract v_5120 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5113 32 64) 24 8) (MInt2Float (extract v_5116 32 64) 24 8)) (MInt2Float (extract v_5120 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5113 64 96) 24 8) (MInt2Float (extract v_5116 64 96) 24 8)) (MInt2Float (extract v_5120 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5113 96 128) 24 8) (MInt2Float (extract v_5116 96 128) 24 8)) (MInt2Float (extract v_5120 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2757 : reg (bv 256)) (v_2758 : reg (bv 256)) (v_2759 : reg (bv 256)) => do
      v_5161 <- getRegister v_2758;
      v_5164 <- getRegister v_2759;
      v_5168 <- getRegister v_2757;
      setRegister (lhs.of_reg v_2759) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 0 32) 24 8) (MInt2Float (extract v_5164 0 32) 24 8)) (MInt2Float (extract v_5168 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 32 64) 24 8) (MInt2Float (extract v_5164 32 64) 24 8)) (MInt2Float (extract v_5168 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 64 96) 24 8) (MInt2Float (extract v_5164 64 96) 24 8)) (MInt2Float (extract v_5168 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 96 128) 24 8) (MInt2Float (extract v_5164 96 128) 24 8)) (MInt2Float (extract v_5168 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 128 160) 24 8) (MInt2Float (extract v_5164 128 160) 24 8)) (MInt2Float (extract v_5168 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 160 192) 24 8) (MInt2Float (extract v_5164 160 192) 24 8)) (MInt2Float (extract v_5168 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 192 224) 24 8) (MInt2Float (extract v_5164 192 224) 24 8)) (MInt2Float (extract v_5168 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5161 224 256) 24 8) (MInt2Float (extract v_5164 224 256) 24 8)) (MInt2Float (extract v_5168 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) (v_2742 : reg (bv 128)) (v_2743 : reg (bv 128)) => do
      v_11045 <- getRegister v_2742;
      v_11048 <- getRegister v_2743;
      v_11052 <- evaluateAddress v_2741;
      v_11053 <- load v_11052 16;
      setRegister (lhs.of_reg v_2743) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11045 0 32) 24 8) (MInt2Float (extract v_11048 0 32) 24 8)) (MInt2Float (extract v_11053 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11045 32 64) 24 8) (MInt2Float (extract v_11048 32 64) 24 8)) (MInt2Float (extract v_11053 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11045 64 96) 24 8) (MInt2Float (extract v_11048 64 96) 24 8)) (MInt2Float (extract v_11053 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11045 96 128) 24 8) (MInt2Float (extract v_11048 96 128) 24 8)) (MInt2Float (extract v_11053 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2752 : Mem) (v_2753 : reg (bv 256)) (v_2754 : reg (bv 256)) => do
      v_11089 <- getRegister v_2753;
      v_11092 <- getRegister v_2754;
      v_11096 <- evaluateAddress v_2752;
      v_11097 <- load v_11096 32;
      setRegister (lhs.of_reg v_2754) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 0 32) 24 8) (MInt2Float (extract v_11092 0 32) 24 8)) (MInt2Float (extract v_11097 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 32 64) 24 8) (MInt2Float (extract v_11092 32 64) 24 8)) (MInt2Float (extract v_11097 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 64 96) 24 8) (MInt2Float (extract v_11092 64 96) 24 8)) (MInt2Float (extract v_11097 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 96 128) 24 8) (MInt2Float (extract v_11092 96 128) 24 8)) (MInt2Float (extract v_11097 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 128 160) 24 8) (MInt2Float (extract v_11092 128 160) 24 8)) (MInt2Float (extract v_11097 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 160 192) 24 8) (MInt2Float (extract v_11092 160 192) 24 8)) (MInt2Float (extract v_11097 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 192 224) 24 8) (MInt2Float (extract v_11092 192 224) 24 8)) (MInt2Float (extract v_11097 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 224 256) 24 8) (MInt2Float (extract v_11092 224 256) 24 8)) (MInt2Float (extract v_11097 224 256) 24 8)) 32)))));
      pure ()
    pat_end
