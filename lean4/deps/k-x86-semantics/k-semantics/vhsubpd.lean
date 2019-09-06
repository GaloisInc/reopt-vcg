def vhsubpd1 : instruction :=
  definst "vhsubpd" $ do
    pattern fun (v_2496 : reg (bv 128)) (v_2497 : reg (bv 128)) (v_2498 : reg (bv 128)) => do
      v_4120 <- getRegister v_2496;
      v_4127 <- getRegister v_2497;
      setRegister (lhs.of_reg v_2498) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4120 64 128) 53 11) (MInt2Float (extract v_4120 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4127 64 128) 53 11) (MInt2Float (extract v_4127 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2507 : reg (bv 256)) (v_2508 : reg (bv 256)) (v_2509 : reg (bv 256)) => do
      v_4141 <- getRegister v_2507;
      v_4148 <- getRegister v_2508;
      setRegister (lhs.of_reg v_2509) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4141 64 128) 53 11) (MInt2Float (extract v_4141 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4148 64 128) 53 11) (MInt2Float (extract v_4148 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4141 192 256) 53 11) (MInt2Float (extract v_4141 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4148 192 256) 53 11) (MInt2Float (extract v_4148 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2491 : Mem) (v_2492 : reg (bv 128)) (v_2493 : reg (bv 128)) => do
      v_9584 <- evaluateAddress v_2491;
      v_9585 <- load v_9584 16;
      v_9592 <- getRegister v_2492;
      setRegister (lhs.of_reg v_2493) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9585 64 128) 53 11) (MInt2Float (extract v_9585 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9592 64 128) 53 11) (MInt2Float (extract v_9592 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2502 : Mem) (v_2503 : reg (bv 256)) (v_2504 : reg (bv 256)) => do
      v_9601 <- evaluateAddress v_2502;
      v_9602 <- load v_9601 32;
      v_9609 <- getRegister v_2503;
      setRegister (lhs.of_reg v_2504) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9602 64 128) 53 11) (MInt2Float (extract v_9602 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9609 64 128) 53 11) (MInt2Float (extract v_9609 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9602 192 256) 53 11) (MInt2Float (extract v_9602 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9609 192 256) 53 11) (MInt2Float (extract v_9609 128 192) 53 11)) 64)));
      pure ()
    pat_end
