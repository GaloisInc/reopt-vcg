def vfnmsub213ps1 : instruction :=
  definst "vfnmsub213ps" $ do
    pattern fun (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) (v_3431 : reg (bv 128)) => do
      v_7672 <- getRegister v_3430;
      v_7675 <- getRegister v_3431;
      v_7680 <- getRegister v_3429;
      setRegister (lhs.of_reg v_3431) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7672 0 32) 24 8) (MInt2Float (extract v_7675 0 32) 24 8))) (MInt2Float (extract v_7680 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7672 32 64) 24 8) (MInt2Float (extract v_7675 32 64) 24 8))) (MInt2Float (extract v_7680 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7672 64 96) 24 8) (MInt2Float (extract v_7675 64 96) 24 8))) (MInt2Float (extract v_7680 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7672 96 128) 24 8) (MInt2Float (extract v_7675 96 128) 24 8))) (MInt2Float (extract v_7680 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3439 : reg (bv 256)) (v_3440 : reg (bv 256)) (v_3441 : reg (bv 256)) => do
      v_7724 <- getRegister v_3440;
      v_7727 <- getRegister v_3441;
      v_7732 <- getRegister v_3439;
      setRegister (lhs.of_reg v_3441) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 0 32) 24 8) (MInt2Float (extract v_7727 0 32) 24 8))) (MInt2Float (extract v_7732 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 32 64) 24 8) (MInt2Float (extract v_7727 32 64) 24 8))) (MInt2Float (extract v_7732 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 64 96) 24 8) (MInt2Float (extract v_7727 64 96) 24 8))) (MInt2Float (extract v_7732 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 96 128) 24 8) (MInt2Float (extract v_7727 96 128) 24 8))) (MInt2Float (extract v_7732 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 128 160) 24 8) (MInt2Float (extract v_7727 128 160) 24 8))) (MInt2Float (extract v_7732 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 160 192) 24 8) (MInt2Float (extract v_7727 160 192) 24 8))) (MInt2Float (extract v_7732 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 192 224) 24 8) (MInt2Float (extract v_7727 192 224) 24 8))) (MInt2Float (extract v_7732 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7724 224 256) 24 8) (MInt2Float (extract v_7727 224 256) 24 8))) (MInt2Float (extract v_7732 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3423 : Mem) (v_3424 : reg (bv 128)) (v_3425 : reg (bv 128)) => do
      v_13342 <- getRegister v_3424;
      v_13345 <- getRegister v_3425;
      v_13350 <- evaluateAddress v_3423;
      v_13351 <- load v_13350 16;
      setRegister (lhs.of_reg v_3425) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13342 0 32) 24 8) (MInt2Float (extract v_13345 0 32) 24 8))) (MInt2Float (extract v_13351 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13342 32 64) 24 8) (MInt2Float (extract v_13345 32 64) 24 8))) (MInt2Float (extract v_13351 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13342 64 96) 24 8) (MInt2Float (extract v_13345 64 96) 24 8))) (MInt2Float (extract v_13351 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13342 96 128) 24 8) (MInt2Float (extract v_13345 96 128) 24 8))) (MInt2Float (extract v_13351 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3434 : Mem) (v_3435 : reg (bv 256)) (v_3436 : reg (bv 256)) => do
      v_13390 <- getRegister v_3435;
      v_13393 <- getRegister v_3436;
      v_13398 <- evaluateAddress v_3434;
      v_13399 <- load v_13398 32;
      setRegister (lhs.of_reg v_3436) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 0 32) 24 8) (MInt2Float (extract v_13393 0 32) 24 8))) (MInt2Float (extract v_13399 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 32 64) 24 8) (MInt2Float (extract v_13393 32 64) 24 8))) (MInt2Float (extract v_13399 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 64 96) 24 8) (MInt2Float (extract v_13393 64 96) 24 8))) (MInt2Float (extract v_13399 64 96) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 96 128) 24 8) (MInt2Float (extract v_13393 96 128) 24 8))) (MInt2Float (extract v_13399 96 128) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 128 160) 24 8) (MInt2Float (extract v_13393 128 160) 24 8))) (MInt2Float (extract v_13399 128 160) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 160 192) 24 8) (MInt2Float (extract v_13393 160 192) 24 8))) (MInt2Float (extract v_13399 160 192) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 192 224) 24 8) (MInt2Float (extract v_13393 192 224) 24 8))) (MInt2Float (extract v_13399 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 224 256) 24 8) (MInt2Float (extract v_13393 224 256) 24 8))) (MInt2Float (extract v_13399 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
