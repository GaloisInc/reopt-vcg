def vfnmsub231pd1 : instruction :=
  definst "vfnmsub231pd" $ do
    pattern fun (v_3408 : reg (bv 128)) (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) => do
      v_7785 <- getRegister v_3409;
      v_7788 <- getRegister v_3408;
      v_7793 <- getRegister v_3410;
      setRegister (lhs.of_reg v_3410) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7785 0 64) 53 11) (MInt2Float (extract v_7788 0 64) 53 11))) (MInt2Float (extract v_7793 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7785 64 128) 53 11) (MInt2Float (extract v_7788 64 128) 53 11))) (MInt2Float (extract v_7793 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3420 : reg (bv 256)) (v_3421 : reg (bv 256)) (v_3422 : reg (bv 256)) => do
      v_7815 <- getRegister v_3421;
      v_7818 <- getRegister v_3420;
      v_7823 <- getRegister v_3422;
      setRegister (lhs.of_reg v_3422) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7815 0 64) 53 11) (MInt2Float (extract v_7818 0 64) 53 11))) (MInt2Float (extract v_7823 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7815 64 128) 53 11) (MInt2Float (extract v_7818 64 128) 53 11))) (MInt2Float (extract v_7823 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7815 128 192) 53 11) (MInt2Float (extract v_7818 128 192) 53 11))) (MInt2Float (extract v_7823 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7815 192 256) 53 11) (MInt2Float (extract v_7818 192 256) 53 11))) (MInt2Float (extract v_7823 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3405 : Mem) (v_3403 : reg (bv 128)) (v_3404 : reg (bv 128)) => do
      v_13420 <- getRegister v_3403;
      v_13423 <- evaluateAddress v_3405;
      v_13424 <- load v_13423 16;
      v_13429 <- getRegister v_3404;
      setRegister (lhs.of_reg v_3404) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13420 0 64) 53 11) (MInt2Float (extract v_13424 0 64) 53 11))) (MInt2Float (extract v_13429 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13420 64 128) 53 11) (MInt2Float (extract v_13424 64 128) 53 11))) (MInt2Float (extract v_13429 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3414 : Mem) (v_3415 : reg (bv 256)) (v_3416 : reg (bv 256)) => do
      v_13446 <- getRegister v_3415;
      v_13449 <- evaluateAddress v_3414;
      v_13450 <- load v_13449 32;
      v_13455 <- getRegister v_3416;
      setRegister (lhs.of_reg v_3416) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13446 0 64) 53 11) (MInt2Float (extract v_13450 0 64) 53 11))) (MInt2Float (extract v_13455 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13446 64 128) 53 11) (MInt2Float (extract v_13450 64 128) 53 11))) (MInt2Float (extract v_13455 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13446 128 192) 53 11) (MInt2Float (extract v_13450 128 192) 53 11))) (MInt2Float (extract v_13455 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13446 192 256) 53 11) (MInt2Float (extract v_13450 192 256) 53 11))) (MInt2Float (extract v_13455 192 256) 53 11)) 64))));
      pure ()
    pat_end
