def vsubpd1 : instruction :=
  definst "vsubpd" $ do
    pattern fun (v_2363 : reg (bv 128)) (v_2364 : reg (bv 128)) (v_2365 : reg (bv 128)) => do
      v_3203 <- getRegister v_2364;
      v_3206 <- getRegister v_2363;
      setRegister (lhs.of_reg v_2365) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3203 0 64) 53 11) (MInt2Float (extract v_3206 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3203 64 128) 53 11) (MInt2Float (extract v_3206 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2373 : reg (bv 256)) (v_2374 : reg (bv 256)) (v_2375 : reg (bv 256)) => do
      v_3224 <- getRegister v_2374;
      v_3227 <- getRegister v_2373;
      setRegister (lhs.of_reg v_2375) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3224 0 64) 53 11) (MInt2Float (extract v_3227 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3224 64 128) 53 11) (MInt2Float (extract v_3227 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3224 128 192) 53 11) (MInt2Float (extract v_3227 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3224 192 256) 53 11) (MInt2Float (extract v_3227 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2356 : Mem) (v_2358 : reg (bv 128)) (v_2359 : reg (bv 128)) => do
      v_6500 <- getRegister v_2358;
      v_6503 <- evaluateAddress v_2356;
      v_6504 <- load v_6503 16;
      setRegister (lhs.of_reg v_2359) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6500 0 64) 53 11) (MInt2Float (extract v_6504 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6500 64 128) 53 11) (MInt2Float (extract v_6504 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2367 : Mem) (v_2368 : reg (bv 256)) (v_2369 : reg (bv 256)) => do
      v_6517 <- getRegister v_2368;
      v_6520 <- evaluateAddress v_2367;
      v_6521 <- load v_6520 32;
      setRegister (lhs.of_reg v_2369) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6517 0 64) 53 11) (MInt2Float (extract v_6521 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6517 64 128) 53 11) (MInt2Float (extract v_6521 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6517 128 192) 53 11) (MInt2Float (extract v_6521 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6517 192 256) 53 11) (MInt2Float (extract v_6521 192 256) 53 11)) 64))));
      pure ()
    pat_end
