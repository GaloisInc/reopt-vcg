def vfmadd231ss1 : instruction :=
  definst "vfmadd231ss" $ do
    pattern fun (v_2605 : reg (bv 128)) (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4753 <- getRegister v_2607;
      v_4755 <- getRegister v_2606;
      v_4758 <- getRegister v_2605;
      setRegister (lhs.of_reg v_2607) (concat (extract v_4753 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4755 96 128) 24 8) (MInt2Float (extract v_4758 96 128) 24 8)) (MInt2Float (extract v_4753 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2602 : Mem) (v_2600 : reg (bv 128)) (v_2601 : reg (bv 128)) => do
      v_10697 <- getRegister v_2601;
      v_10699 <- getRegister v_2600;
      v_10702 <- evaluateAddress v_2602;
      v_10703 <- load v_10702 4;
      setRegister (lhs.of_reg v_2601) (concat (extract v_10697 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10699 96 128) 24 8) (MInt2Float v_10703 24 8)) (MInt2Float (extract v_10697 96 128) 24 8)) 32));
      pure ()
    pat_end
