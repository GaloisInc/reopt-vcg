def vfmadd132ss1 : instruction :=
  definst "vfmadd132ss" $ do
    pattern fun (v_2562 : reg (bv 128)) (v_2563 : reg (bv 128)) (v_2564 : reg (bv 128)) => do
      v_4341 <- getRegister v_2564;
      v_4345 <- getRegister v_2562;
      v_4349 <- getRegister v_2563;
      setRegister (lhs.of_reg v_2564) (concat (extract v_4341 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4341 96 128) 24 8) (MInt2Float (extract v_4345 96 128) 24 8)) (MInt2Float (extract v_4349 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2557 : reg (bv 128)) (v_2558 : reg (bv 128)) => do
      v_10354 <- getRegister v_2558;
      v_10358 <- evaluateAddress v_2559;
      v_10359 <- load v_10358 4;
      v_10362 <- getRegister v_2557;
      setRegister (lhs.of_reg v_2558) (concat (extract v_10354 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10354 96 128) 24 8) (MInt2Float v_10359 24 8)) (MInt2Float (extract v_10362 96 128) 24 8)) 32));
      pure ()
    pat_end
