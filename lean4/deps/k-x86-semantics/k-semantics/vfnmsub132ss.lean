def vfnmsub132ss1 : instruction :=
  definst "vfnmsub132ss" $ do
    pattern fun (v_3420 : reg (bv 128)) (v_3421 : reg (bv 128)) (v_3422 : reg (bv 128)) => do
      v_7596 <- getRegister v_3422;
      v_7600 <- getRegister v_3420;
      v_7605 <- getRegister v_3421;
      setRegister (lhs.of_reg v_3422) (concat (extract v_7596 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7596 96 128) 24 8) (MInt2Float (extract v_7600 96 128) 24 8))) (MInt2Float (extract v_7605 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3417 : Mem) (v_3415 : reg (bv 128)) (v_3416 : reg (bv 128)) => do
      v_13279 <- getRegister v_3416;
      v_13283 <- evaluateAddress v_3417;
      v_13284 <- load v_13283 4;
      v_13288 <- getRegister v_3415;
      setRegister (lhs.of_reg v_3416) (concat (extract v_13279 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13279 96 128) 24 8) (MInt2Float v_13284 24 8))) (MInt2Float (extract v_13288 96 128) 24 8)) 32));
      pure ()
    pat_end
