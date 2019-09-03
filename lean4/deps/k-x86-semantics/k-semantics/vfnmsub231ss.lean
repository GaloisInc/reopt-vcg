def vfnmsub231ss1 : instruction :=
  definst "vfnmsub231ss" $ do
    pattern fun (v_3463 : reg (bv 128)) (v_3464 : reg (bv 128)) (v_3465 : reg (bv 128)) => do
      v_8049 <- getRegister v_3465;
      v_8051 <- getRegister v_3464;
      v_8054 <- getRegister v_3463;
      setRegister (lhs.of_reg v_3465) (concat (extract v_8049 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8051 96 128) 24 8) (MInt2Float (extract v_8054 96 128) 24 8))) (MInt2Float (extract v_8049 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3460 : Mem) (v_3458 : reg (bv 128)) (v_3459 : reg (bv 128)) => do
      v_13663 <- getRegister v_3459;
      v_13665 <- getRegister v_3458;
      v_13668 <- evaluateAddress v_3460;
      v_13669 <- load v_13668 4;
      setRegister (lhs.of_reg v_3459) (concat (extract v_13663 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13665 96 128) 24 8) (MInt2Float v_13669 24 8))) (MInt2Float (extract v_13663 96 128) 24 8)) 32));
      pure ()
    pat_end
