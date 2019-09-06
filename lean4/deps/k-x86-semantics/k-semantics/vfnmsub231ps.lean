def vfnmsub231ps1 : instruction :=
  definst "vfnmsub231ps" $ do
    pattern fun (v_3519 : reg (bv 128)) (v_3520 : reg (bv 128)) (v_3521 : reg (bv 128)) => do
      v_7971 <- getRegister v_3520;
      v_7974 <- getRegister v_3519;
      v_7979 <- getRegister v_3521;
      setRegister (lhs.of_reg v_3521) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7971 0 32) 24 8) (MInt2Float (extract v_7974 0 32) 24 8))) (MInt2Float (extract v_7979 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7971 32 64) 24 8) (MInt2Float (extract v_7974 32 64) 24 8))) (MInt2Float (extract v_7979 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7971 64 96) 24 8) (MInt2Float (extract v_7974 64 96) 24 8))) (MInt2Float (extract v_7979 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7971 96 128) 24 8) (MInt2Float (extract v_7974 96 128) 24 8))) (MInt2Float (extract v_7979 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3533 : reg (bv 256)) (v_3534 : reg (bv 256)) (v_3535 : reg (bv 256)) => do
      v_8023 <- getRegister v_3534;
      v_8026 <- getRegister v_3533;
      v_8031 <- getRegister v_3535;
      setRegister (lhs.of_reg v_3535) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 0 32) 24 8) (MInt2Float (extract v_8026 0 32) 24 8))) (MInt2Float (extract v_8031 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 32 64) 24 8) (MInt2Float (extract v_8026 32 64) 24 8))) (MInt2Float (extract v_8031 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 64 96) 24 8) (MInt2Float (extract v_8026 64 96) 24 8))) (MInt2Float (extract v_8031 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 96 128) 24 8) (MInt2Float (extract v_8026 96 128) 24 8))) (MInt2Float (extract v_8031 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 128 160) 24 8) (MInt2Float (extract v_8026 128 160) 24 8))) (MInt2Float (extract v_8031 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 160 192) 24 8) (MInt2Float (extract v_8026 160 192) 24 8))) (MInt2Float (extract v_8031 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 192 224) 24 8) (MInt2Float (extract v_8026 192 224) 24 8))) (MInt2Float (extract v_8031 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8023 224 256) 24 8) (MInt2Float (extract v_8026 224 256) 24 8))) (MInt2Float (extract v_8031 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3516 : Mem) (v_3514 : reg (bv 128)) (v_3515 : reg (bv 128)) => do
      v_13615 <- getRegister v_3514;
      v_13618 <- evaluateAddress v_3516;
      v_13619 <- load v_13618 16;
      v_13624 <- getRegister v_3515;
      setRegister (lhs.of_reg v_3515) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13615 0 32) 24 8) (MInt2Float (extract v_13619 0 32) 24 8))) (MInt2Float (extract v_13624 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13615 32 64) 24 8) (MInt2Float (extract v_13619 32 64) 24 8))) (MInt2Float (extract v_13624 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13615 64 96) 24 8) (MInt2Float (extract v_13619 64 96) 24 8))) (MInt2Float (extract v_13624 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13615 96 128) 24 8) (MInt2Float (extract v_13619 96 128) 24 8))) (MInt2Float (extract v_13624 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3525 : Mem) (v_3528 : reg (bv 256)) (v_3529 : reg (bv 256)) => do
      v_13663 <- getRegister v_3528;
      v_13666 <- evaluateAddress v_3525;
      v_13667 <- load v_13666 32;
      v_13672 <- getRegister v_3529;
      setRegister (lhs.of_reg v_3529) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 0 32) 24 8) (MInt2Float (extract v_13667 0 32) 24 8))) (MInt2Float (extract v_13672 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 32 64) 24 8) (MInt2Float (extract v_13667 32 64) 24 8))) (MInt2Float (extract v_13672 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 64 96) 24 8) (MInt2Float (extract v_13667 64 96) 24 8))) (MInt2Float (extract v_13672 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 96 128) 24 8) (MInt2Float (extract v_13667 96 128) 24 8))) (MInt2Float (extract v_13672 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 128 160) 24 8) (MInt2Float (extract v_13667 128 160) 24 8))) (MInt2Float (extract v_13672 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 160 192) 24 8) (MInt2Float (extract v_13667 160 192) 24 8))) (MInt2Float (extract v_13672 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 192 224) 24 8) (MInt2Float (extract v_13667 192 224) 24 8))) (MInt2Float (extract v_13672 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13663 224 256) 24 8) (MInt2Float (extract v_13667 224 256) 24 8))) (MInt2Float (extract v_13672 224 256) 24 8)) 32)))));
      pure ()
    pat_end
