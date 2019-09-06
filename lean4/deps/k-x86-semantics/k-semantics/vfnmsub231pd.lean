def vfnmsub231pd1 : instruction :=
  definst "vfnmsub231pd" $ do
    pattern fun (v_3497 : reg (bv 128)) (v_3498 : reg (bv 128)) (v_3499 : reg (bv 128)) => do
      v_7889 <- getRegister v_3498;
      v_7892 <- getRegister v_3497;
      v_7897 <- getRegister v_3499;
      setRegister (lhs.of_reg v_3499) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7889 0 64) 53 11) (MInt2Float (extract v_7892 0 64) 53 11))) (MInt2Float (extract v_7897 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7889 64 128) 53 11) (MInt2Float (extract v_7892 64 128) 53 11))) (MInt2Float (extract v_7897 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3511 : reg (bv 256)) (v_3512 : reg (bv 256)) (v_3513 : reg (bv 256)) => do
      v_7919 <- getRegister v_3512;
      v_7922 <- getRegister v_3511;
      v_7927 <- getRegister v_3513;
      setRegister (lhs.of_reg v_3513) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 0 64) 53 11) (MInt2Float (extract v_7922 0 64) 53 11))) (MInt2Float (extract v_7927 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 64 128) 53 11) (MInt2Float (extract v_7922 64 128) 53 11))) (MInt2Float (extract v_7927 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 128 192) 53 11) (MInt2Float (extract v_7922 128 192) 53 11))) (MInt2Float (extract v_7927 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7919 192 256) 53 11) (MInt2Float (extract v_7922 192 256) 53 11))) (MInt2Float (extract v_7927 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3494 : Mem) (v_3492 : reg (bv 128)) (v_3493 : reg (bv 128)) => do
      v_13541 <- getRegister v_3492;
      v_13544 <- evaluateAddress v_3494;
      v_13545 <- load v_13544 16;
      v_13550 <- getRegister v_3493;
      setRegister (lhs.of_reg v_3493) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13541 0 64) 53 11) (MInt2Float (extract v_13545 0 64) 53 11))) (MInt2Float (extract v_13550 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13541 64 128) 53 11) (MInt2Float (extract v_13545 64 128) 53 11))) (MInt2Float (extract v_13550 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3503 : Mem) (v_3506 : reg (bv 256)) (v_3507 : reg (bv 256)) => do
      v_13567 <- getRegister v_3506;
      v_13570 <- evaluateAddress v_3503;
      v_13571 <- load v_13570 32;
      v_13576 <- getRegister v_3507;
      setRegister (lhs.of_reg v_3507) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13567 0 64) 53 11) (MInt2Float (extract v_13571 0 64) 53 11))) (MInt2Float (extract v_13576 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13567 64 128) 53 11) (MInt2Float (extract v_13571 64 128) 53 11))) (MInt2Float (extract v_13576 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13567 128 192) 53 11) (MInt2Float (extract v_13571 128 192) 53 11))) (MInt2Float (extract v_13576 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13567 192 256) 53 11) (MInt2Float (extract v_13571 192 256) 53 11))) (MInt2Float (extract v_13576 192 256) 53 11)) 64))));
      pure ()
    pat_end
