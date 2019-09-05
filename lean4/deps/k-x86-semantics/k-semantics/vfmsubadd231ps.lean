def vfmsubadd231ps1 : instruction :=
  definst "vfmsubadd231ps" $ do
    pattern fun (v_3121 : reg (bv 128)) (v_3122 : reg (bv 128)) (v_3123 : reg (bv 128)) => do
      v_6705 <- getRegister v_3122;
      v_6708 <- getRegister v_3121;
      v_6712 <- getRegister v_3123;
      setRegister (lhs.of_reg v_3123) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6705 0 32) 24 8) (MInt2Float (extract v_6708 0 32) 24 8)) (MInt2Float (extract v_6712 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6705 32 64) 24 8) (MInt2Float (extract v_6708 32 64) 24 8)) (MInt2Float (extract v_6712 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6705 64 96) 24 8) (MInt2Float (extract v_6708 64 96) 24 8)) (MInt2Float (extract v_6712 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6705 96 128) 24 8) (MInt2Float (extract v_6708 96 128) 24 8)) (MInt2Float (extract v_6712 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3131 : reg (bv 256)) (v_3132 : reg (bv 256)) (v_3133 : reg (bv 256)) => do
      v_6753 <- getRegister v_3132;
      v_6756 <- getRegister v_3131;
      v_6760 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3133) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 0 32) 24 8) (MInt2Float (extract v_6756 0 32) 24 8)) (MInt2Float (extract v_6760 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 32 64) 24 8) (MInt2Float (extract v_6756 32 64) 24 8)) (MInt2Float (extract v_6760 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 64 96) 24 8) (MInt2Float (extract v_6756 64 96) 24 8)) (MInt2Float (extract v_6760 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 96 128) 24 8) (MInt2Float (extract v_6756 96 128) 24 8)) (MInt2Float (extract v_6760 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 128 160) 24 8) (MInt2Float (extract v_6756 128 160) 24 8)) (MInt2Float (extract v_6760 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 160 192) 24 8) (MInt2Float (extract v_6756 160 192) 24 8)) (MInt2Float (extract v_6760 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 192 224) 24 8) (MInt2Float (extract v_6756 192 224) 24 8)) (MInt2Float (extract v_6760 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6753 224 256) 24 8) (MInt2Float (extract v_6756 224 256) 24 8)) (MInt2Float (extract v_6760 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) (v_3117 : reg (bv 128)) => do
      v_12495 <- getRegister v_3116;
      v_12498 <- evaluateAddress v_3115;
      v_12499 <- load v_12498 16;
      v_12503 <- getRegister v_3117;
      setRegister (lhs.of_reg v_3117) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12495 0 32) 24 8) (MInt2Float (extract v_12499 0 32) 24 8)) (MInt2Float (extract v_12503 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12495 32 64) 24 8) (MInt2Float (extract v_12499 32 64) 24 8)) (MInt2Float (extract v_12503 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12495 64 96) 24 8) (MInt2Float (extract v_12499 64 96) 24 8)) (MInt2Float (extract v_12503 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12495 96 128) 24 8) (MInt2Float (extract v_12499 96 128) 24 8)) (MInt2Float (extract v_12503 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3126 : Mem) (v_3127 : reg (bv 256)) (v_3128 : reg (bv 256)) => do
      v_12539 <- getRegister v_3127;
      v_12542 <- evaluateAddress v_3126;
      v_12543 <- load v_12542 32;
      v_12547 <- getRegister v_3128;
      setRegister (lhs.of_reg v_3128) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 0 32) 24 8) (MInt2Float (extract v_12543 0 32) 24 8)) (MInt2Float (extract v_12547 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 32 64) 24 8) (MInt2Float (extract v_12543 32 64) 24 8)) (MInt2Float (extract v_12547 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 64 96) 24 8) (MInt2Float (extract v_12543 64 96) 24 8)) (MInt2Float (extract v_12547 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 96 128) 24 8) (MInt2Float (extract v_12543 96 128) 24 8)) (MInt2Float (extract v_12547 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 128 160) 24 8) (MInt2Float (extract v_12543 128 160) 24 8)) (MInt2Float (extract v_12547 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 160 192) 24 8) (MInt2Float (extract v_12543 160 192) 24 8)) (MInt2Float (extract v_12547 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 192 224) 24 8) (MInt2Float (extract v_12543 192 224) 24 8)) (MInt2Float (extract v_12547 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12539 224 256) 24 8) (MInt2Float (extract v_12543 224 256) 24 8)) (MInt2Float (extract v_12547 224 256) 24 8)) 32)))));
      pure ()
    pat_end
