def vfmadd132ss1 : instruction :=
  definst "vfmadd132ss" $ do
    pattern fun (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_4314 <- getRegister v_2540;
      v_4318 <- getRegister v_2538;
      v_4322 <- getRegister v_2539;
      setRegister (lhs.of_reg v_2540) (concat (extract v_4314 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4314 96 128) 24 8) (MInt2Float (extract v_4318 96 128) 24 8)) (MInt2Float (extract v_4322 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_10327 <- getRegister v_2534;
      v_10331 <- evaluateAddress v_2532;
      v_10332 <- load v_10331 4;
      v_10335 <- getRegister v_2533;
      setRegister (lhs.of_reg v_2534) (concat (extract v_10327 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10327 96 128) 24 8) (MInt2Float v_10332 24 8)) (MInt2Float (extract v_10335 96 128) 24 8)) 32));
      pure ()
    pat_end
