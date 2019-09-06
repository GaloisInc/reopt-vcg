def vfmsub132ps1 : instruction :=
  definst "vfmsub132ps" $ do
    pattern fun (v_2859 : reg (bv 128)) (v_2860 : reg (bv 128)) (v_2861 : reg (bv 128)) => do
      v_5564 <- getRegister v_2861;
      v_5567 <- getRegister v_2859;
      v_5571 <- getRegister v_2860;
      setRegister (lhs.of_reg v_2861) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5564 0 32) 24 8) (MInt2Float (extract v_5567 0 32) 24 8)) (MInt2Float (extract v_5571 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5564 32 64) 24 8) (MInt2Float (extract v_5567 32 64) 24 8)) (MInt2Float (extract v_5571 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5564 64 96) 24 8) (MInt2Float (extract v_5567 64 96) 24 8)) (MInt2Float (extract v_5571 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5564 96 128) 24 8) (MInt2Float (extract v_5567 96 128) 24 8)) (MInt2Float (extract v_5571 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2873 : reg (bv 256)) (v_2874 : reg (bv 256)) (v_2875 : reg (bv 256)) => do
      v_5612 <- getRegister v_2875;
      v_5615 <- getRegister v_2873;
      v_5619 <- getRegister v_2874;
      setRegister (lhs.of_reg v_2875) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 0 32) 24 8) (MInt2Float (extract v_5615 0 32) 24 8)) (MInt2Float (extract v_5619 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 32 64) 24 8) (MInt2Float (extract v_5615 32 64) 24 8)) (MInt2Float (extract v_5619 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 64 96) 24 8) (MInt2Float (extract v_5615 64 96) 24 8)) (MInt2Float (extract v_5619 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 96 128) 24 8) (MInt2Float (extract v_5615 96 128) 24 8)) (MInt2Float (extract v_5619 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 128 160) 24 8) (MInt2Float (extract v_5615 128 160) 24 8)) (MInt2Float (extract v_5619 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 160 192) 24 8) (MInt2Float (extract v_5615 160 192) 24 8)) (MInt2Float (extract v_5619 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 192 224) 24 8) (MInt2Float (extract v_5615 192 224) 24 8)) (MInt2Float (extract v_5619 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5612 224 256) 24 8) (MInt2Float (extract v_5615 224 256) 24 8)) (MInt2Float (extract v_5619 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2856 : Mem) (v_2854 : reg (bv 128)) (v_2855 : reg (bv 128)) => do
      v_11464 <- getRegister v_2855;
      v_11467 <- evaluateAddress v_2856;
      v_11468 <- load v_11467 16;
      v_11472 <- getRegister v_2854;
      setRegister (lhs.of_reg v_2855) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11464 0 32) 24 8) (MInt2Float (extract v_11468 0 32) 24 8)) (MInt2Float (extract v_11472 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11464 32 64) 24 8) (MInt2Float (extract v_11468 32 64) 24 8)) (MInt2Float (extract v_11472 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11464 64 96) 24 8) (MInt2Float (extract v_11468 64 96) 24 8)) (MInt2Float (extract v_11472 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11464 96 128) 24 8) (MInt2Float (extract v_11468 96 128) 24 8)) (MInt2Float (extract v_11472 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2865 : Mem) (v_2868 : reg (bv 256)) (v_2869 : reg (bv 256)) => do
      v_11508 <- getRegister v_2869;
      v_11511 <- evaluateAddress v_2865;
      v_11512 <- load v_11511 32;
      v_11516 <- getRegister v_2868;
      setRegister (lhs.of_reg v_2869) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 0 32) 24 8) (MInt2Float (extract v_11512 0 32) 24 8)) (MInt2Float (extract v_11516 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 32 64) 24 8) (MInt2Float (extract v_11512 32 64) 24 8)) (MInt2Float (extract v_11516 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 64 96) 24 8) (MInt2Float (extract v_11512 64 96) 24 8)) (MInt2Float (extract v_11516 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 96 128) 24 8) (MInt2Float (extract v_11512 96 128) 24 8)) (MInt2Float (extract v_11516 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 128 160) 24 8) (MInt2Float (extract v_11512 128 160) 24 8)) (MInt2Float (extract v_11516 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 160 192) 24 8) (MInt2Float (extract v_11512 160 192) 24 8)) (MInt2Float (extract v_11516 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 192 224) 24 8) (MInt2Float (extract v_11512 192 224) 24 8)) (MInt2Float (extract v_11516 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11508 224 256) 24 8) (MInt2Float (extract v_11512 224 256) 24 8)) (MInt2Float (extract v_11516 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
