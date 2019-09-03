def vfmadd132ss1 : instruction :=
  definst "vfmadd132ss" $ do
    pattern fun (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) => do
      v_4254 <- getRegister v_2475;
      v_4258 <- getRegister v_2473;
      v_4262 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2475) (concat (extract v_4254 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4254 96 128) 24 8) (MInt2Float (extract v_4258 96 128) 24 8)) (MInt2Float (extract v_4262 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2468 : reg (bv 128)) (v_2469 : reg (bv 128)) => do
      v_10250 <- getRegister v_2469;
      v_10254 <- evaluateAddress v_2470;
      v_10255 <- load v_10254 4;
      v_10258 <- getRegister v_2468;
      setRegister (lhs.of_reg v_2469) (concat (extract v_10250 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10250 96 128) 24 8) (MInt2Float v_10255 24 8)) (MInt2Float (extract v_10258 96 128) 24 8)) 32));
      pure ()
    pat_end
