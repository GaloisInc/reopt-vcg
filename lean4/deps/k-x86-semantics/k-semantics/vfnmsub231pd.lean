def vfnmsub231pd1 : instruction :=
  definst "vfnmsub231pd" $ do
    pattern fun (v_3473 : reg (bv 128)) (v_3474 : reg (bv 128)) (v_3475 : reg (bv 128)) => do
      v_7862 <- getRegister v_3474;
      v_7865 <- getRegister v_3473;
      v_7870 <- getRegister v_3475;
      setRegister (lhs.of_reg v_3475) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7862 0 64) 53 11) (MInt2Float (extract v_7865 0 64) 53 11))) (MInt2Float (extract v_7870 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7862 64 128) 53 11) (MInt2Float (extract v_7865 64 128) 53 11))) (MInt2Float (extract v_7870 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3483 : reg (bv 256)) (v_3484 : reg (bv 256)) (v_3485 : reg (bv 256)) => do
      v_7892 <- getRegister v_3484;
      v_7895 <- getRegister v_3483;
      v_7900 <- getRegister v_3485;
      setRegister (lhs.of_reg v_3485) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7892 0 64) 53 11) (MInt2Float (extract v_7895 0 64) 53 11))) (MInt2Float (extract v_7900 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7892 64 128) 53 11) (MInt2Float (extract v_7895 64 128) 53 11))) (MInt2Float (extract v_7900 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7892 128 192) 53 11) (MInt2Float (extract v_7895 128 192) 53 11))) (MInt2Float (extract v_7900 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7892 192 256) 53 11) (MInt2Float (extract v_7895 192 256) 53 11))) (MInt2Float (extract v_7900 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3467 : Mem) (v_3468 : reg (bv 128)) (v_3469 : reg (bv 128)) => do
      v_13514 <- getRegister v_3468;
      v_13517 <- evaluateAddress v_3467;
      v_13518 <- load v_13517 16;
      v_13523 <- getRegister v_3469;
      setRegister (lhs.of_reg v_3469) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13514 0 64) 53 11) (MInt2Float (extract v_13518 0 64) 53 11))) (MInt2Float (extract v_13523 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13514 64 128) 53 11) (MInt2Float (extract v_13518 64 128) 53 11))) (MInt2Float (extract v_13523 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3478 : Mem) (v_3479 : reg (bv 256)) (v_3480 : reg (bv 256)) => do
      v_13540 <- getRegister v_3479;
      v_13543 <- evaluateAddress v_3478;
      v_13544 <- load v_13543 32;
      v_13549 <- getRegister v_3480;
      setRegister (lhs.of_reg v_3480) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13540 0 64) 53 11) (MInt2Float (extract v_13544 0 64) 53 11))) (MInt2Float (extract v_13549 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13540 64 128) 53 11) (MInt2Float (extract v_13544 64 128) 53 11))) (MInt2Float (extract v_13549 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13540 128 192) 53 11) (MInt2Float (extract v_13544 128 192) 53 11))) (MInt2Float (extract v_13549 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13540 192 256) 53 11) (MInt2Float (extract v_13544 192 256) 53 11))) (MInt2Float (extract v_13549 192 256) 53 11)) 64))));
      pure ()
    pat_end
