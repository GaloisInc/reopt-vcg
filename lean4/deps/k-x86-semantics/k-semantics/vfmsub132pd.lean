def vfmsub132pd1 : instruction :=
  definst "vfmsub132pd" $ do
    pattern fun (v_2837 : reg (bv 128)) (v_2838 : reg (bv 128)) (v_2839 : reg (bv 128)) => do
      v_5488 <- getRegister v_2839;
      v_5491 <- getRegister v_2837;
      v_5495 <- getRegister v_2838;
      setRegister (lhs.of_reg v_2839) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5488 0 64) 53 11) (MInt2Float (extract v_5491 0 64) 53 11)) (MInt2Float (extract v_5495 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5488 64 128) 53 11) (MInt2Float (extract v_5491 64 128) 53 11)) (MInt2Float (extract v_5495 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2851 : reg (bv 256)) (v_2852 : reg (bv 256)) (v_2853 : reg (bv 256)) => do
      v_5516 <- getRegister v_2853;
      v_5519 <- getRegister v_2851;
      v_5523 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2853) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5516 0 64) 53 11) (MInt2Float (extract v_5519 0 64) 53 11)) (MInt2Float (extract v_5523 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5516 64 128) 53 11) (MInt2Float (extract v_5519 64 128) 53 11)) (MInt2Float (extract v_5523 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5516 128 192) 53 11) (MInt2Float (extract v_5519 128 192) 53 11)) (MInt2Float (extract v_5523 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5516 192 256) 53 11) (MInt2Float (extract v_5519 192 256) 53 11)) (MInt2Float (extract v_5523 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2834 : Mem) (v_2832 : reg (bv 128)) (v_2833 : reg (bv 128)) => do
      v_11396 <- getRegister v_2833;
      v_11399 <- evaluateAddress v_2834;
      v_11400 <- load v_11399 16;
      v_11404 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2833) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11396 0 64) 53 11) (MInt2Float (extract v_11400 0 64) 53 11)) (MInt2Float (extract v_11404 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11396 64 128) 53 11) (MInt2Float (extract v_11400 64 128) 53 11)) (MInt2Float (extract v_11404 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2843 : Mem) (v_2846 : reg (bv 256)) (v_2847 : reg (bv 256)) => do
      v_11420 <- getRegister v_2847;
      v_11423 <- evaluateAddress v_2843;
      v_11424 <- load v_11423 32;
      v_11428 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2847) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11420 0 64) 53 11) (MInt2Float (extract v_11424 0 64) 53 11)) (MInt2Float (extract v_11428 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11420 64 128) 53 11) (MInt2Float (extract v_11424 64 128) 53 11)) (MInt2Float (extract v_11428 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11420 128 192) 53 11) (MInt2Float (extract v_11424 128 192) 53 11)) (MInt2Float (extract v_11428 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11420 192 256) 53 11) (MInt2Float (extract v_11424 192 256) 53 11)) (MInt2Float (extract v_11428 192 256) 53 11)) 64))));
      pure ()
    pat_end
