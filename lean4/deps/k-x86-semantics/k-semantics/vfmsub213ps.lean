def vfmsub213ps1 : instruction :=
  definst "vfmsub213ps" $ do
    pattern fun (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) (v_2903 : reg (bv 128)) => do
      v_5792 <- getRegister v_2902;
      v_5795 <- getRegister v_2903;
      v_5799 <- getRegister v_2901;
      setRegister (lhs.of_reg v_2903) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5792 0 32) 24 8) (MInt2Float (extract v_5795 0 32) 24 8)) (MInt2Float (extract v_5799 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5792 32 64) 24 8) (MInt2Float (extract v_5795 32 64) 24 8)) (MInt2Float (extract v_5799 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5792 64 96) 24 8) (MInt2Float (extract v_5795 64 96) 24 8)) (MInt2Float (extract v_5799 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5792 96 128) 24 8) (MInt2Float (extract v_5795 96 128) 24 8)) (MInt2Float (extract v_5799 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2911 : reg (bv 256)) (v_2912 : reg (bv 256)) (v_2913 : reg (bv 256)) => do
      v_5840 <- getRegister v_2912;
      v_5843 <- getRegister v_2913;
      v_5847 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2913) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 0 32) 24 8) (MInt2Float (extract v_5843 0 32) 24 8)) (MInt2Float (extract v_5847 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 32 64) 24 8) (MInt2Float (extract v_5843 32 64) 24 8)) (MInt2Float (extract v_5847 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 64 96) 24 8) (MInt2Float (extract v_5843 64 96) 24 8)) (MInt2Float (extract v_5847 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 96 128) 24 8) (MInt2Float (extract v_5843 96 128) 24 8)) (MInt2Float (extract v_5847 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 128 160) 24 8) (MInt2Float (extract v_5843 128 160) 24 8)) (MInt2Float (extract v_5847 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 160 192) 24 8) (MInt2Float (extract v_5843 160 192) 24 8)) (MInt2Float (extract v_5847 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 192 224) 24 8) (MInt2Float (extract v_5843 192 224) 24 8)) (MInt2Float (extract v_5847 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5840 224 256) 24 8) (MInt2Float (extract v_5843 224 256) 24 8)) (MInt2Float (extract v_5847 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2895 : Mem) (v_2896 : reg (bv 128)) (v_2897 : reg (bv 128)) => do
      v_11666 <- getRegister v_2896;
      v_11669 <- getRegister v_2897;
      v_11673 <- evaluateAddress v_2895;
      v_11674 <- load v_11673 16;
      setRegister (lhs.of_reg v_2897) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11666 0 32) 24 8) (MInt2Float (extract v_11669 0 32) 24 8)) (MInt2Float (extract v_11674 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11666 32 64) 24 8) (MInt2Float (extract v_11669 32 64) 24 8)) (MInt2Float (extract v_11674 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11666 64 96) 24 8) (MInt2Float (extract v_11669 64 96) 24 8)) (MInt2Float (extract v_11674 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11666 96 128) 24 8) (MInt2Float (extract v_11669 96 128) 24 8)) (MInt2Float (extract v_11674 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2906 : Mem) (v_2907 : reg (bv 256)) (v_2908 : reg (bv 256)) => do
      v_11710 <- getRegister v_2907;
      v_11713 <- getRegister v_2908;
      v_11717 <- evaluateAddress v_2906;
      v_11718 <- load v_11717 32;
      setRegister (lhs.of_reg v_2908) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 0 32) 24 8) (MInt2Float (extract v_11713 0 32) 24 8)) (MInt2Float (extract v_11718 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 32 64) 24 8) (MInt2Float (extract v_11713 32 64) 24 8)) (MInt2Float (extract v_11718 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 64 96) 24 8) (MInt2Float (extract v_11713 64 96) 24 8)) (MInt2Float (extract v_11718 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 96 128) 24 8) (MInt2Float (extract v_11713 96 128) 24 8)) (MInt2Float (extract v_11718 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 128 160) 24 8) (MInt2Float (extract v_11713 128 160) 24 8)) (MInt2Float (extract v_11718 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 160 192) 24 8) (MInt2Float (extract v_11713 160 192) 24 8)) (MInt2Float (extract v_11718 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 192 224) 24 8) (MInt2Float (extract v_11713 192 224) 24 8)) (MInt2Float (extract v_11718 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11710 224 256) 24 8) (MInt2Float (extract v_11713 224 256) 24 8)) (MInt2Float (extract v_11718 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
