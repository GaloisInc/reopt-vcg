def vfmadd213ss1 : instruction :=
  definst "vfmadd213ss" $ do
    pattern fun (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) (v_2541 : reg (bv 128)) => do
      v_4512 <- getRegister v_2541;
      v_4514 <- getRegister v_2540;
      v_4520 <- getRegister v_2539;
      setRegister (lhs.of_reg v_2541) (concat (extract v_4512 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4514 96 128) 24 8) (MInt2Float (extract v_4512 96 128) 24 8)) (MInt2Float (extract v_4520 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2536 : Mem) (v_2534 : reg (bv 128)) (v_2535 : reg (bv 128)) => do
      v_10482 <- getRegister v_2535;
      v_10484 <- getRegister v_2534;
      v_10490 <- evaluateAddress v_2536;
      v_10491 <- load v_10490 4;
      setRegister (lhs.of_reg v_2535) (concat (extract v_10482 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10484 96 128) 24 8) (MInt2Float (extract v_10482 96 128) 24 8)) (MInt2Float v_10491 24 8)) 32));
      pure ()
    pat_end
