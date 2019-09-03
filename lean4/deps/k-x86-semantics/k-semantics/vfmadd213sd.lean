def vfmadd213sd1 : instruction :=
  definst "vfmadd213sd" $ do
    pattern fun (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) (v_2530 : reg (bv 128)) => do
      v_4492 <- getRegister v_2530;
      v_4494 <- getRegister v_2529;
      v_4500 <- getRegister v_2528;
      setRegister (lhs.of_reg v_2530) (concat (extract v_4492 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4494 64 128) 53 11) (MInt2Float (extract v_4492 64 128) 53 11)) (MInt2Float (extract v_4500 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2525 : Mem) (v_2523 : reg (bv 128)) (v_2524 : reg (bv 128)) => do
      v_10467 <- getRegister v_2524;
      v_10469 <- getRegister v_2523;
      v_10475 <- evaluateAddress v_2525;
      v_10476 <- load v_10475 8;
      setRegister (lhs.of_reg v_2524) (concat (extract v_10467 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10469 64 128) 53 11) (MInt2Float (extract v_10467 64 128) 53 11)) (MInt2Float v_10476 53 11)) 64));
      pure ()
    pat_end
