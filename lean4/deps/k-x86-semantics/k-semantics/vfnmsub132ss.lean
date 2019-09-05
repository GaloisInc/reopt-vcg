def vfnmsub132ss1 : instruction :=
  definst "vfnmsub132ss" $ do
    pattern fun (v_3396 : reg (bv 128)) (v_3397 : reg (bv 128)) (v_3398 : reg (bv 128)) => do
      v_7569 <- getRegister v_3398;
      v_7573 <- getRegister v_3396;
      v_7578 <- getRegister v_3397;
      setRegister (lhs.of_reg v_3398) (concat (extract v_7569 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7569 96 128) 24 8) (MInt2Float (extract v_7573 96 128) 24 8))) (MInt2Float (extract v_7578 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3390 : Mem) (v_3391 : reg (bv 128)) (v_3392 : reg (bv 128)) => do
      v_13252 <- getRegister v_3392;
      v_13256 <- evaluateAddress v_3390;
      v_13257 <- load v_13256 4;
      v_13261 <- getRegister v_3391;
      setRegister (lhs.of_reg v_3392) (concat (extract v_13252 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13252 96 128) 24 8) (MInt2Float v_13257 24 8))) (MInt2Float (extract v_13261 96 128) 24 8)) 32));
      pure ()
    pat_end
