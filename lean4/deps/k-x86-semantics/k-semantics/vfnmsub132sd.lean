def vfnmsub132sd1 : instruction :=
  definst "vfnmsub132sd" $ do
    pattern fun (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) (v_3411 : reg (bv 128)) => do
      v_7575 <- getRegister v_3411;
      v_7579 <- getRegister v_3409;
      v_7584 <- getRegister v_3410;
      setRegister (lhs.of_reg v_3411) (concat (extract v_7575 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7575 64 128) 53 11) (MInt2Float (extract v_7579 64 128) 53 11))) (MInt2Float (extract v_7584 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3406 : Mem) (v_3404 : reg (bv 128)) (v_3405 : reg (bv 128)) => do
      v_13263 <- getRegister v_3405;
      v_13267 <- evaluateAddress v_3406;
      v_13268 <- load v_13267 8;
      v_13272 <- getRegister v_3404;
      setRegister (lhs.of_reg v_3405) (concat (extract v_13263 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13263 64 128) 53 11) (MInt2Float v_13268 53 11))) (MInt2Float (extract v_13272 64 128) 53 11)) 64));
      pure ()
    pat_end
