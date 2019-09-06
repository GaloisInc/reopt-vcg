def vfmadd213sd1 : instruction :=
  definst "vfmadd213sd" $ do
    pattern fun (v_2617 : reg (bv 128)) (v_2618 : reg (bv 128)) (v_2619 : reg (bv 128)) => do
      v_4579 <- getRegister v_2619;
      v_4581 <- getRegister v_2618;
      v_4587 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2619) (concat (extract v_4579 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4581 64 128) 53 11) (MInt2Float (extract v_4579 64 128) 53 11)) (MInt2Float (extract v_4587 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) (v_2612 : reg (bv 128)) (v_2613 : reg (bv 128)) => do
      v_10571 <- getRegister v_2613;
      v_10573 <- getRegister v_2612;
      v_10579 <- evaluateAddress v_2614;
      v_10580 <- load v_10579 8;
      setRegister (lhs.of_reg v_2613) (concat (extract v_10571 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10573 64 128) 53 11) (MInt2Float (extract v_10571 64 128) 53 11)) (MInt2Float v_10580 53 11)) 64));
      pure ()
    pat_end
