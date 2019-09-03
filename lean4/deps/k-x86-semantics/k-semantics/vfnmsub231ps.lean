def vfnmsub231ps1 : instruction :=
  definst "vfnmsub231ps" $ do
    pattern fun (v_3430 : reg (bv 128)) (v_3431 : reg (bv 128)) (v_3432 : reg (bv 128)) => do
      v_7867 <- getRegister v_3431;
      v_7870 <- getRegister v_3430;
      v_7875 <- getRegister v_3432;
      setRegister (lhs.of_reg v_3432) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7867 0 32) 24 8) (MInt2Float (extract v_7870 0 32) 24 8))) (MInt2Float (extract v_7875 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7867 32 64) 24 8) (MInt2Float (extract v_7870 32 64) 24 8))) (MInt2Float (extract v_7875 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7867 64 96) 24 8) (MInt2Float (extract v_7870 64 96) 24 8))) (MInt2Float (extract v_7875 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7867 96 128) 24 8) (MInt2Float (extract v_7870 96 128) 24 8))) (MInt2Float (extract v_7875 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3442 : reg (bv 256)) (v_3443 : reg (bv 256)) (v_3444 : reg (bv 256)) => do
      v_7919 <- getRegister v_3443;
      v_7922 <- getRegister v_3442;
      v_7927 <- getRegister v_3444;
      setRegister (lhs.of_reg v_3444) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 0 32) 24 8) (MInt2Float (extract v_7922 0 32) 24 8))) (MInt2Float (extract v_7927 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 32 64) 24 8) (MInt2Float (extract v_7922 32 64) 24 8))) (MInt2Float (extract v_7927 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 64 96) 24 8) (MInt2Float (extract v_7922 64 96) 24 8))) (MInt2Float (extract v_7927 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 96 128) 24 8) (MInt2Float (extract v_7922 96 128) 24 8))) (MInt2Float (extract v_7927 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 128 160) 24 8) (MInt2Float (extract v_7922 128 160) 24 8))) (MInt2Float (extract v_7927 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 160 192) 24 8) (MInt2Float (extract v_7922 160 192) 24 8))) (MInt2Float (extract v_7927 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 192 224) 24 8) (MInt2Float (extract v_7922 192 224) 24 8))) (MInt2Float (extract v_7927 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 224 256) 24 8) (MInt2Float (extract v_7922 224 256) 24 8))) (MInt2Float (extract v_7927 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3427 : Mem) (v_3425 : reg (bv 128)) (v_3426 : reg (bv 128)) => do
      v_13494 <- getRegister v_3425;
      v_13497 <- evaluateAddress v_3427;
      v_13498 <- load v_13497 16;
      v_13503 <- getRegister v_3426;
      setRegister (lhs.of_reg v_3426) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13494 0 32) 24 8) (MInt2Float (extract v_13498 0 32) 24 8))) (MInt2Float (extract v_13503 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13494 32 64) 24 8) (MInt2Float (extract v_13498 32 64) 24 8))) (MInt2Float (extract v_13503 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13494 64 96) 24 8) (MInt2Float (extract v_13498 64 96) 24 8))) (MInt2Float (extract v_13503 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13494 96 128) 24 8) (MInt2Float (extract v_13498 96 128) 24 8))) (MInt2Float (extract v_13503 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3436 : Mem) (v_3437 : reg (bv 256)) (v_3438 : reg (bv 256)) => do
      v_13542 <- getRegister v_3437;
      v_13545 <- evaluateAddress v_3436;
      v_13546 <- load v_13545 32;
      v_13551 <- getRegister v_3438;
      setRegister (lhs.of_reg v_3438) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 0 32) 24 8) (MInt2Float (extract v_13546 0 32) 24 8))) (MInt2Float (extract v_13551 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 32 64) 24 8) (MInt2Float (extract v_13546 32 64) 24 8))) (MInt2Float (extract v_13551 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 64 96) 24 8) (MInt2Float (extract v_13546 64 96) 24 8))) (MInt2Float (extract v_13551 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 96 128) 24 8) (MInt2Float (extract v_13546 96 128) 24 8))) (MInt2Float (extract v_13551 96 128) 24 8)) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 128 160) 24 8) (MInt2Float (extract v_13546 128 160) 24 8))) (MInt2Float (extract v_13551 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 160 192) 24 8) (MInt2Float (extract v_13546 160 192) 24 8))) (MInt2Float (extract v_13551 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 192 224) 24 8) (MInt2Float (extract v_13546 192 224) 24 8))) (MInt2Float (extract v_13551 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13542 224 256) 24 8) (MInt2Float (extract v_13546 224 256) 24 8))) (MInt2Float (extract v_13551 224 256) 24 8)) 32)))));
      pure ()
    pat_end
