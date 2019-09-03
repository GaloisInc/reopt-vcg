def vfmsub213ps1 : instruction :=
  definst "vfmsub213ps" $ do
    pattern fun (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) (v_2838 : reg (bv 128)) => do
      v_5725 <- getRegister v_2837;
      v_5728 <- getRegister v_2838;
      v_5732 <- getRegister v_2836;
      setRegister (lhs.of_reg v_2838) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5725 0 32) 24 8) (MInt2Float (extract v_5728 0 32) 24 8)) (MInt2Float (extract v_5732 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5725 32 64) 24 8) (MInt2Float (extract v_5728 32 64) 24 8)) (MInt2Float (extract v_5732 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5725 64 96) 24 8) (MInt2Float (extract v_5728 64 96) 24 8)) (MInt2Float (extract v_5732 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5725 96 128) 24 8) (MInt2Float (extract v_5728 96 128) 24 8)) (MInt2Float (extract v_5732 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2848 : reg (bv 256)) (v_2849 : reg (bv 256)) (v_2850 : reg (bv 256)) => do
      v_5773 <- getRegister v_2849;
      v_5776 <- getRegister v_2850;
      v_5780 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2850) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 0 32) 24 8) (MInt2Float (extract v_5776 0 32) 24 8)) (MInt2Float (extract v_5780 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 32 64) 24 8) (MInt2Float (extract v_5776 32 64) 24 8)) (MInt2Float (extract v_5780 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 64 96) 24 8) (MInt2Float (extract v_5776 64 96) 24 8)) (MInt2Float (extract v_5780 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 96 128) 24 8) (MInt2Float (extract v_5776 96 128) 24 8)) (MInt2Float (extract v_5780 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 128 160) 24 8) (MInt2Float (extract v_5776 128 160) 24 8)) (MInt2Float (extract v_5780 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 160 192) 24 8) (MInt2Float (extract v_5776 160 192) 24 8)) (MInt2Float (extract v_5780 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 192 224) 24 8) (MInt2Float (extract v_5776 192 224) 24 8)) (MInt2Float (extract v_5780 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5773 224 256) 24 8) (MInt2Float (extract v_5776 224 256) 24 8)) (MInt2Float (extract v_5780 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2833 : Mem) (v_2831 : reg (bv 128)) (v_2832 : reg (bv 128)) => do
      v_11582 <- getRegister v_2831;
      v_11585 <- getRegister v_2832;
      v_11589 <- evaluateAddress v_2833;
      v_11590 <- load v_11589 16;
      setRegister (lhs.of_reg v_2832) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11582 0 32) 24 8) (MInt2Float (extract v_11585 0 32) 24 8)) (MInt2Float (extract v_11590 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11582 32 64) 24 8) (MInt2Float (extract v_11585 32 64) 24 8)) (MInt2Float (extract v_11590 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11582 64 96) 24 8) (MInt2Float (extract v_11585 64 96) 24 8)) (MInt2Float (extract v_11590 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11582 96 128) 24 8) (MInt2Float (extract v_11585 96 128) 24 8)) (MInt2Float (extract v_11590 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2842 : Mem) (v_2843 : reg (bv 256)) (v_2844 : reg (bv 256)) => do
      v_11626 <- getRegister v_2843;
      v_11629 <- getRegister v_2844;
      v_11633 <- evaluateAddress v_2842;
      v_11634 <- load v_11633 32;
      setRegister (lhs.of_reg v_2844) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 0 32) 24 8) (MInt2Float (extract v_11629 0 32) 24 8)) (MInt2Float (extract v_11634 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 32 64) 24 8) (MInt2Float (extract v_11629 32 64) 24 8)) (MInt2Float (extract v_11634 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 64 96) 24 8) (MInt2Float (extract v_11629 64 96) 24 8)) (MInt2Float (extract v_11634 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 96 128) 24 8) (MInt2Float (extract v_11629 96 128) 24 8)) (MInt2Float (extract v_11634 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 128 160) 24 8) (MInt2Float (extract v_11629 128 160) 24 8)) (MInt2Float (extract v_11634 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 160 192) 24 8) (MInt2Float (extract v_11629 160 192) 24 8)) (MInt2Float (extract v_11634 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 192 224) 24 8) (MInt2Float (extract v_11629 192 224) 24 8)) (MInt2Float (extract v_11634 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11626 224 256) 24 8) (MInt2Float (extract v_11629 224 256) 24 8)) (MInt2Float (extract v_11634 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
