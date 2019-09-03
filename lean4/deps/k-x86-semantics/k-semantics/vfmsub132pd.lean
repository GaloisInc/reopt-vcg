def vfmsub132pd1 : instruction :=
  definst "vfmsub132pd" $ do
    pattern fun (v_2748 : reg (bv 128)) (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) => do
      v_5394 <- getRegister v_2750;
      v_5397 <- getRegister v_2748;
      v_5401 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2750) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5394 0 64) 53 11) (MInt2Float (extract v_5397 0 64) 53 11)) (MInt2Float (extract v_5401 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5394 64 128) 53 11) (MInt2Float (extract v_5397 64 128) 53 11)) (MInt2Float (extract v_5401 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2760 : reg (bv 256)) (v_2761 : reg (bv 256)) (v_2762 : reg (bv 256)) => do
      v_5422 <- getRegister v_2762;
      v_5425 <- getRegister v_2760;
      v_5429 <- getRegister v_2761;
      setRegister (lhs.of_reg v_2762) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5422 0 64) 53 11) (MInt2Float (extract v_5425 0 64) 53 11)) (MInt2Float (extract v_5429 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5422 64 128) 53 11) (MInt2Float (extract v_5425 64 128) 53 11)) (MInt2Float (extract v_5429 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5422 128 192) 53 11) (MInt2Float (extract v_5425 128 192) 53 11)) (MInt2Float (extract v_5429 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5422 192 256) 53 11) (MInt2Float (extract v_5425 192 256) 53 11)) (MInt2Float (extract v_5429 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2745 : Mem) (v_2743 : reg (bv 128)) (v_2744 : reg (bv 128)) => do
      v_11285 <- getRegister v_2744;
      v_11288 <- evaluateAddress v_2745;
      v_11289 <- load v_11288 16;
      v_11293 <- getRegister v_2743;
      setRegister (lhs.of_reg v_2744) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 0 64) 53 11) (MInt2Float (extract v_11289 0 64) 53 11)) (MInt2Float (extract v_11293 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11285 64 128) 53 11) (MInt2Float (extract v_11289 64 128) 53 11)) (MInt2Float (extract v_11293 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2754 : Mem) (v_2755 : reg (bv 256)) (v_2756 : reg (bv 256)) => do
      v_11309 <- getRegister v_2756;
      v_11312 <- evaluateAddress v_2754;
      v_11313 <- load v_11312 32;
      v_11317 <- getRegister v_2755;
      setRegister (lhs.of_reg v_2756) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11309 0 64) 53 11) (MInt2Float (extract v_11313 0 64) 53 11)) (MInt2Float (extract v_11317 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11309 64 128) 53 11) (MInt2Float (extract v_11313 64 128) 53 11)) (MInt2Float (extract v_11317 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11309 128 192) 53 11) (MInt2Float (extract v_11313 128 192) 53 11)) (MInt2Float (extract v_11317 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11309 192 256) 53 11) (MInt2Float (extract v_11313 192 256) 53 11)) (MInt2Float (extract v_11317 192 256) 53 11)) 64))));
      pure ()
    pat_end
