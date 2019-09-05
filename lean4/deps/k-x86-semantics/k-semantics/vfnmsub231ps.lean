def vfnmsub231ps1 : instruction :=
  definst "vfnmsub231ps" $ do
    pattern fun (v_3495 : reg (bv 128)) (v_3496 : reg (bv 128)) (v_3497 : reg (bv 128)) => do
      v_7944 <- getRegister v_3496;
      v_7947 <- getRegister v_3495;
      v_7952 <- getRegister v_3497;
      setRegister (lhs.of_reg v_3497) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7944 0 32) 24 8) (MInt2Float (extract v_7947 0 32) 24 8))) (MInt2Float (extract v_7952 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7944 32 64) 24 8) (MInt2Float (extract v_7947 32 64) 24 8))) (MInt2Float (extract v_7952 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7944 64 96) 24 8) (MInt2Float (extract v_7947 64 96) 24 8))) (MInt2Float (extract v_7952 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7944 96 128) 24 8) (MInt2Float (extract v_7947 96 128) 24 8))) (MInt2Float (extract v_7952 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3505 : reg (bv 256)) (v_3506 : reg (bv 256)) (v_3507 : reg (bv 256)) => do
      v_7996 <- getRegister v_3506;
      v_7999 <- getRegister v_3505;
      v_8004 <- getRegister v_3507;
      setRegister (lhs.of_reg v_3507) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 0 32) 24 8) (MInt2Float (extract v_7999 0 32) 24 8))) (MInt2Float (extract v_8004 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 32 64) 24 8) (MInt2Float (extract v_7999 32 64) 24 8))) (MInt2Float (extract v_8004 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 64 96) 24 8) (MInt2Float (extract v_7999 64 96) 24 8))) (MInt2Float (extract v_8004 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 96 128) 24 8) (MInt2Float (extract v_7999 96 128) 24 8))) (MInt2Float (extract v_8004 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 128 160) 24 8) (MInt2Float (extract v_7999 128 160) 24 8))) (MInt2Float (extract v_8004 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 160 192) 24 8) (MInt2Float (extract v_7999 160 192) 24 8))) (MInt2Float (extract v_8004 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 192 224) 24 8) (MInt2Float (extract v_7999 192 224) 24 8))) (MInt2Float (extract v_8004 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7996 224 256) 24 8) (MInt2Float (extract v_7999 224 256) 24 8))) (MInt2Float (extract v_8004 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3489 : Mem) (v_3490 : reg (bv 128)) (v_3491 : reg (bv 128)) => do
      v_13588 <- getRegister v_3490;
      v_13591 <- evaluateAddress v_3489;
      v_13592 <- load v_13591 16;
      v_13597 <- getRegister v_3491;
      setRegister (lhs.of_reg v_3491) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13588 0 32) 24 8) (MInt2Float (extract v_13592 0 32) 24 8))) (MInt2Float (extract v_13597 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13588 32 64) 24 8) (MInt2Float (extract v_13592 32 64) 24 8))) (MInt2Float (extract v_13597 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13588 64 96) 24 8) (MInt2Float (extract v_13592 64 96) 24 8))) (MInt2Float (extract v_13597 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13588 96 128) 24 8) (MInt2Float (extract v_13592 96 128) 24 8))) (MInt2Float (extract v_13597 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3500 : Mem) (v_3501 : reg (bv 256)) (v_3502 : reg (bv 256)) => do
      v_13636 <- getRegister v_3501;
      v_13639 <- evaluateAddress v_3500;
      v_13640 <- load v_13639 32;
      v_13645 <- getRegister v_3502;
      setRegister (lhs.of_reg v_3502) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 0 32) 24 8) (MInt2Float (extract v_13640 0 32) 24 8))) (MInt2Float (extract v_13645 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 32 64) 24 8) (MInt2Float (extract v_13640 32 64) 24 8))) (MInt2Float (extract v_13645 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 64 96) 24 8) (MInt2Float (extract v_13640 64 96) 24 8))) (MInt2Float (extract v_13645 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 96 128) 24 8) (MInt2Float (extract v_13640 96 128) 24 8))) (MInt2Float (extract v_13645 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 128 160) 24 8) (MInt2Float (extract v_13640 128 160) 24 8))) (MInt2Float (extract v_13645 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 160 192) 24 8) (MInt2Float (extract v_13640 160 192) 24 8))) (MInt2Float (extract v_13645 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 192 224) 24 8) (MInt2Float (extract v_13640 192 224) 24 8))) (MInt2Float (extract v_13645 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13636 224 256) 24 8) (MInt2Float (extract v_13640 224 256) 24 8))) (MInt2Float (extract v_13645 224 256) 24 8)) 32)))));
      pure ()
    pat_end
