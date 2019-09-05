def vfnmsub213sd1 : instruction :=
  definst "vfnmsub213sd" $ do
    pattern fun (v_3451 : reg (bv 128)) (v_3452 : reg (bv 128)) (v_3453 : reg (bv 128)) => do
      v_7820 <- getRegister v_3453;
      v_7822 <- getRegister v_3452;
      v_7829 <- getRegister v_3451;
      setRegister (lhs.of_reg v_3453) (concat (extract v_7820 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7822 64 128) 53 11) (MInt2Float (extract v_7820 64 128) 53 11))) (MInt2Float (extract v_7829 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3445 : Mem) (v_3446 : reg (bv 128)) (v_3447 : reg (bv 128)) => do
      v_13482 <- getRegister v_3447;
      v_13484 <- getRegister v_3446;
      v_13491 <- evaluateAddress v_3445;
      v_13492 <- load v_13491 8;
      setRegister (lhs.of_reg v_3447) (concat (extract v_13482 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13484 64 128) 53 11) (MInt2Float (extract v_13482 64 128) 53 11))) (MInt2Float v_13492 53 11)) 64));
      pure ()
    pat_end
