def vhsubpd1 : instruction :=
  definst "vhsubpd" $ do
    pattern fun (v_2408 : reg (bv 128)) (v_2409 : reg (bv 128)) (v_2410 : reg (bv 128)) => do
      v_4029 <- getRegister v_2408;
      v_4036 <- getRegister v_2409;
      setRegister (lhs.of_reg v_2410) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4029 64 128) 53 11) (MInt2Float (extract v_4029 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4036 64 128) 53 11) (MInt2Float (extract v_4036 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2419 : reg (bv 256)) (v_2420 : reg (bv 256)) (v_2421 : reg (bv 256)) => do
      v_4050 <- getRegister v_2419;
      v_4057 <- getRegister v_2420;
      setRegister (lhs.of_reg v_2421) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4050 64 128) 53 11) (MInt2Float (extract v_4050 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4057 64 128) 53 11) (MInt2Float (extract v_4057 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4050 192 256) 53 11) (MInt2Float (extract v_4050 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4057 192 256) 53 11) (MInt2Float (extract v_4057 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2402 : Mem) (v_2403 : reg (bv 128)) (v_2404 : reg (bv 128)) => do
      v_9667 <- evaluateAddress v_2402;
      v_9668 <- load v_9667 16;
      v_9675 <- getRegister v_2403;
      setRegister (lhs.of_reg v_2404) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9668 64 128) 53 11) (MInt2Float (extract v_9668 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9675 64 128) 53 11) (MInt2Float (extract v_9675 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2413 : Mem) (v_2414 : reg (bv 256)) (v_2415 : reg (bv 256)) => do
      v_9684 <- evaluateAddress v_2413;
      v_9685 <- load v_9684 32;
      v_9692 <- getRegister v_2414;
      setRegister (lhs.of_reg v_2415) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9685 64 128) 53 11) (MInt2Float (extract v_9685 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9692 64 128) 53 11) (MInt2Float (extract v_9692 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9685 192 256) 53 11) (MInt2Float (extract v_9685 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9692 192 256) 53 11) (MInt2Float (extract v_9692 128 192) 53 11)) 64)));
      pure ()
    pat_end
