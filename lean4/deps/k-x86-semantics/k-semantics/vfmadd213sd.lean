def vfmadd213sd1 : instruction :=
  definst "vfmadd213sd" $ do
    pattern fun (v_2593 : reg (bv 128)) (v_2594 : reg (bv 128)) (v_2595 : reg (bv 128)) => do
      v_4552 <- getRegister v_2595;
      v_4554 <- getRegister v_2594;
      v_4560 <- getRegister v_2593;
      setRegister (lhs.of_reg v_2595) (concat (extract v_4552 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4554 64 128) 53 11) (MInt2Float (extract v_4552 64 128) 53 11)) (MInt2Float (extract v_4560 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2587 : Mem) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_10544 <- getRegister v_2589;
      v_10546 <- getRegister v_2588;
      v_10552 <- evaluateAddress v_2587;
      v_10553 <- load v_10552 8;
      setRegister (lhs.of_reg v_2589) (concat (extract v_10544 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10546 64 128) 53 11) (MInt2Float (extract v_10544 64 128) 53 11)) (MInt2Float v_10553 53 11)) 64));
      pure ()
    pat_end
