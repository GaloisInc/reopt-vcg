def vfmadd231sd1 : instruction :=
  definst "vfmadd231sd" $ do
    pattern fun (v_2594 : reg (bv 128)) (v_2595 : reg (bv 128)) (v_2596 : reg (bv 128)) => do
      v_4730 <- getRegister v_2596;
      v_4732 <- getRegister v_2595;
      v_4735 <- getRegister v_2594;
      setRegister (lhs.of_reg v_2596) (concat (extract v_4730 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4732 64 128) 53 11) (MInt2Float (extract v_4735 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_4730 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2591 : Mem) (v_2589 : reg (bv 128)) (v_2590 : reg (bv 128)) => do
      v_10679 <- getRegister v_2590;
      v_10681 <- getRegister v_2589;
      v_10684 <- evaluateAddress v_2591;
      v_10685 <- load v_10684 8;
      setRegister (lhs.of_reg v_2590) (concat (extract v_10679 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10681 64 128) 53 11) (MInt2Float v_10685 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MInt2Float (extract v_10679 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end
