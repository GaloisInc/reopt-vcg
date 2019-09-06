def vfnmsub213ps1 : instruction :=
  definst "vfnmsub213ps" $ do
    pattern fun (v_3453 : reg (bv 128)) (v_3454 : reg (bv 128)) (v_3455 : reg (bv 128)) => do
      v_7699 <- getRegister v_3454;
      v_7702 <- getRegister v_3455;
      v_7707 <- getRegister v_3453;
      setRegister (lhs.of_reg v_3455) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7699 0 32) 24 8) (MInt2Float (extract v_7702 0 32) 24 8))) (MInt2Float (extract v_7707 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7699 32 64) 24 8) (MInt2Float (extract v_7702 32 64) 24 8))) (MInt2Float (extract v_7707 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7699 64 96) 24 8) (MInt2Float (extract v_7702 64 96) 24 8))) (MInt2Float (extract v_7707 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7699 96 128) 24 8) (MInt2Float (extract v_7702 96 128) 24 8))) (MInt2Float (extract v_7707 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3467 : reg (bv 256)) (v_3468 : reg (bv 256)) (v_3469 : reg (bv 256)) => do
      v_7751 <- getRegister v_3468;
      v_7754 <- getRegister v_3469;
      v_7759 <- getRegister v_3467;
      setRegister (lhs.of_reg v_3469) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 0 32) 24 8) (MInt2Float (extract v_7754 0 32) 24 8))) (MInt2Float (extract v_7759 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 32 64) 24 8) (MInt2Float (extract v_7754 32 64) 24 8))) (MInt2Float (extract v_7759 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 64 96) 24 8) (MInt2Float (extract v_7754 64 96) 24 8))) (MInt2Float (extract v_7759 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 96 128) 24 8) (MInt2Float (extract v_7754 96 128) 24 8))) (MInt2Float (extract v_7759 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 128 160) 24 8) (MInt2Float (extract v_7754 128 160) 24 8))) (MInt2Float (extract v_7759 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 160 192) 24 8) (MInt2Float (extract v_7754 160 192) 24 8))) (MInt2Float (extract v_7759 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 192 224) 24 8) (MInt2Float (extract v_7754 192 224) 24 8))) (MInt2Float (extract v_7759 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7751 224 256) 24 8) (MInt2Float (extract v_7754 224 256) 24 8))) (MInt2Float (extract v_7759 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3450 : Mem) (v_3448 : reg (bv 128)) (v_3449 : reg (bv 128)) => do
      v_13369 <- getRegister v_3448;
      v_13372 <- getRegister v_3449;
      v_13377 <- evaluateAddress v_3450;
      v_13378 <- load v_13377 16;
      setRegister (lhs.of_reg v_3449) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13369 0 32) 24 8) (MInt2Float (extract v_13372 0 32) 24 8))) (MInt2Float (extract v_13378 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13369 32 64) 24 8) (MInt2Float (extract v_13372 32 64) 24 8))) (MInt2Float (extract v_13378 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13369 64 96) 24 8) (MInt2Float (extract v_13372 64 96) 24 8))) (MInt2Float (extract v_13378 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13369 96 128) 24 8) (MInt2Float (extract v_13372 96 128) 24 8))) (MInt2Float (extract v_13378 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3459 : Mem) (v_3462 : reg (bv 256)) (v_3463 : reg (bv 256)) => do
      v_13417 <- getRegister v_3462;
      v_13420 <- getRegister v_3463;
      v_13425 <- evaluateAddress v_3459;
      v_13426 <- load v_13425 32;
      setRegister (lhs.of_reg v_3463) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 0 32) 24 8) (MInt2Float (extract v_13420 0 32) 24 8))) (MInt2Float (extract v_13426 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 32 64) 24 8) (MInt2Float (extract v_13420 32 64) 24 8))) (MInt2Float (extract v_13426 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 64 96) 24 8) (MInt2Float (extract v_13420 64 96) 24 8))) (MInt2Float (extract v_13426 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 96 128) 24 8) (MInt2Float (extract v_13420 96 128) 24 8))) (MInt2Float (extract v_13426 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 128 160) 24 8) (MInt2Float (extract v_13420 128 160) 24 8))) (MInt2Float (extract v_13426 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 160 192) 24 8) (MInt2Float (extract v_13420 160 192) 24 8))) (MInt2Float (extract v_13426 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 192 224) 24 8) (MInt2Float (extract v_13420 192 224) 24 8))) (MInt2Float (extract v_13426 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13417 224 256) 24 8) (MInt2Float (extract v_13420 224 256) 24 8))) (MInt2Float (extract v_13426 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
