def vfmadd213ss1 : instruction :=
  definst "vfmadd213ss" $ do
    pattern fun (v_2604 : reg (bv 128)) (v_2605 : reg (bv 128)) (v_2606 : reg (bv 128)) => do
      v_4572 <- getRegister v_2606;
      v_4574 <- getRegister v_2605;
      v_4580 <- getRegister v_2604;
      setRegister (lhs.of_reg v_2606) (concat (extract v_4572 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4574 96 128) 24 8) (MInt2Float (extract v_4572 96 128) 24 8)) (MInt2Float (extract v_4580 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2598 : Mem) (v_2599 : reg (bv 128)) (v_2600 : reg (bv 128)) => do
      v_10559 <- getRegister v_2600;
      v_10561 <- getRegister v_2599;
      v_10567 <- evaluateAddress v_2598;
      v_10568 <- load v_10567 4;
      setRegister (lhs.of_reg v_2600) (concat (extract v_10559 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10561 96 128) 24 8) (MInt2Float (extract v_10559 96 128) 24 8)) (MInt2Float v_10568 24 8)) 32));
      pure ()
    pat_end
