def vfnmsub213sd1 : instruction :=
  definst "vfnmsub213sd" $ do
    pattern fun (v_3475 : reg (bv 128)) (v_3476 : reg (bv 128)) (v_3477 : reg (bv 128)) => do
      v_7847 <- getRegister v_3477;
      v_7849 <- getRegister v_3476;
      v_7856 <- getRegister v_3475;
      setRegister (lhs.of_reg v_3477) (concat (extract v_7847 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7849 64 128) 53 11) (MInt2Float (extract v_7847 64 128) 53 11))) (MInt2Float (extract v_7856 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3472 : Mem) (v_3470 : reg (bv 128)) (v_3471 : reg (bv 128)) => do
      v_13509 <- getRegister v_3471;
      v_13511 <- getRegister v_3470;
      v_13518 <- evaluateAddress v_3472;
      v_13519 <- load v_13518 8;
      setRegister (lhs.of_reg v_3471) (concat (extract v_13509 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13511 64 128) 53 11) (MInt2Float (extract v_13509 64 128) 53 11))) (MInt2Float v_13519 53 11)) 64));
      pure ()
    pat_end
