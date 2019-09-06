def vfmadd213ss1 : instruction :=
  definst "vfmadd213ss" $ do
    pattern fun (v_2628 : reg (bv 128)) (v_2629 : reg (bv 128)) (v_2630 : reg (bv 128)) => do
      v_4599 <- getRegister v_2630;
      v_4601 <- getRegister v_2629;
      v_4607 <- getRegister v_2628;
      setRegister (lhs.of_reg v_2630) (concat (extract v_4599 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4601 96 128) 24 8) (MInt2Float (extract v_4599 96 128) 24 8)) (MInt2Float (extract v_4607 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2625 : Mem) (v_2623 : reg (bv 128)) (v_2624 : reg (bv 128)) => do
      v_10586 <- getRegister v_2624;
      v_10588 <- getRegister v_2623;
      v_10594 <- evaluateAddress v_2625;
      v_10595 <- load v_10594 4;
      setRegister (lhs.of_reg v_2624) (concat (extract v_10586 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10588 96 128) 24 8) (MInt2Float (extract v_10586 96 128) 24 8)) (MInt2Float v_10595 24 8)) 32));
      pure ()
    pat_end
