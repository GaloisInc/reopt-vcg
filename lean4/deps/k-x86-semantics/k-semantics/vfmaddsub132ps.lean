def vfmaddsub132ps1 : instruction :=
  definst "vfmaddsub132ps" $ do
    pattern fun (v_2638 : reg (bv 128)) (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) => do
      v_4834 <- getRegister v_2640;
      v_4837 <- getRegister v_2638;
      v_4841 <- getRegister v_2639;
      setRegister (lhs.of_reg v_2640) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4834 0 32) 24 8) (MInt2Float (extract v_4837 0 32) 24 8)) (MInt2Float (extract v_4841 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4834 32 64) 24 8) (MInt2Float (extract v_4837 32 64) 24 8)) (MInt2Float (extract v_4841 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4834 64 96) 24 8) (MInt2Float (extract v_4837 64 96) 24 8)) (MInt2Float (extract v_4841 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4834 96 128) 24 8) (MInt2Float (extract v_4837 96 128) 24 8)) (MInt2Float (extract v_4841 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2650 : reg (bv 256)) (v_2651 : reg (bv 256)) (v_2652 : reg (bv 256)) => do
      v_4882 <- getRegister v_2652;
      v_4885 <- getRegister v_2650;
      v_4889 <- getRegister v_2651;
      setRegister (lhs.of_reg v_2652) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 0 32) 24 8) (MInt2Float (extract v_4885 0 32) 24 8)) (MInt2Float (extract v_4889 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 32 64) 24 8) (MInt2Float (extract v_4885 32 64) 24 8)) (MInt2Float (extract v_4889 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 64 96) 24 8) (MInt2Float (extract v_4885 64 96) 24 8)) (MInt2Float (extract v_4889 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 96 128) 24 8) (MInt2Float (extract v_4885 96 128) 24 8)) (MInt2Float (extract v_4889 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 128 160) 24 8) (MInt2Float (extract v_4885 128 160) 24 8)) (MInt2Float (extract v_4889 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 160 192) 24 8) (MInt2Float (extract v_4885 160 192) 24 8)) (MInt2Float (extract v_4889 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 192 224) 24 8) (MInt2Float (extract v_4885 192 224) 24 8)) (MInt2Float (extract v_4889 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4882 224 256) 24 8) (MInt2Float (extract v_4885 224 256) 24 8)) (MInt2Float (extract v_4889 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2635 : Mem) (v_2633 : reg (bv 128)) (v_2634 : reg (bv 128)) => do
      v_10765 <- getRegister v_2634;
      v_10768 <- evaluateAddress v_2635;
      v_10769 <- load v_10768 16;
      v_10773 <- getRegister v_2633;
      setRegister (lhs.of_reg v_2634) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10765 0 32) 24 8) (MInt2Float (extract v_10769 0 32) 24 8)) (MInt2Float (extract v_10773 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10765 32 64) 24 8) (MInt2Float (extract v_10769 32 64) 24 8)) (MInt2Float (extract v_10773 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10765 64 96) 24 8) (MInt2Float (extract v_10769 64 96) 24 8)) (MInt2Float (extract v_10773 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10765 96 128) 24 8) (MInt2Float (extract v_10769 96 128) 24 8)) (MInt2Float (extract v_10773 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2644 : Mem) (v_2645 : reg (bv 256)) (v_2646 : reg (bv 256)) => do
      v_10809 <- getRegister v_2646;
      v_10812 <- evaluateAddress v_2644;
      v_10813 <- load v_10812 32;
      v_10817 <- getRegister v_2645;
      setRegister (lhs.of_reg v_2646) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 0 32) 24 8) (MInt2Float (extract v_10813 0 32) 24 8)) (MInt2Float (extract v_10817 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 32 64) 24 8) (MInt2Float (extract v_10813 32 64) 24 8)) (MInt2Float (extract v_10817 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 64 96) 24 8) (MInt2Float (extract v_10813 64 96) 24 8)) (MInt2Float (extract v_10817 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 96 128) 24 8) (MInt2Float (extract v_10813 96 128) 24 8)) (MInt2Float (extract v_10817 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 128 160) 24 8) (MInt2Float (extract v_10813 128 160) 24 8)) (MInt2Float (extract v_10817 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 160 192) 24 8) (MInt2Float (extract v_10813 160 192) 24 8)) (MInt2Float (extract v_10817 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 192 224) 24 8) (MInt2Float (extract v_10813 192 224) 24 8)) (MInt2Float (extract v_10817 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10809 224 256) 24 8) (MInt2Float (extract v_10813 224 256) 24 8)) (MInt2Float (extract v_10817 224 256) 24 8)) 32)))));
      pure ()
    pat_end
