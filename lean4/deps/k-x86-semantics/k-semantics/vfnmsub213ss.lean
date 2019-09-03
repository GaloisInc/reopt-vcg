def vfnmsub213ss1 : instruction :=
  definst "vfnmsub213ss" $ do
    pattern fun (v_3397 : reg (bv 128)) (v_3398 : reg (bv 128)) (v_3399 : reg (bv 128)) => do
      v_7764 <- getRegister v_3399;
      v_7766 <- getRegister v_3398;
      v_7773 <- getRegister v_3397;
      setRegister (lhs.of_reg v_3399) (concat (extract v_7764 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7766 96 128) 24 8) (MInt2Float (extract v_7764 96 128) 24 8))) (MInt2Float (extract v_7773 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3394 : Mem) (v_3392 : reg (bv 128)) (v_3393 : reg (bv 128)) => do
      v_13404 <- getRegister v_3393;
      v_13406 <- getRegister v_3392;
      v_13413 <- evaluateAddress v_3394;
      v_13414 <- load v_13413 4;
      setRegister (lhs.of_reg v_3393) (concat (extract v_13404 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13406 96 128) 24 8) (MInt2Float (extract v_13404 96 128) 24 8))) (MInt2Float v_13414 24 8)) 32));
      pure ()
    pat_end
