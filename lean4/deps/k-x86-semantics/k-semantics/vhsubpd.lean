def vhsubpd1 : instruction :=
  definst "vhsubpd" $ do
    pattern fun (v_2471 : reg (bv 128)) (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) => do
      v_4093 <- getRegister v_2471;
      v_4100 <- getRegister v_2472;
      setRegister (lhs.of_reg v_2473) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4093 64 128) 53 11) (MInt2Float (extract v_4093 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4100 64 128) 53 11) (MInt2Float (extract v_4100 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2483 : reg (bv 256)) (v_2484 : reg (bv 256)) (v_2485 : reg (bv 256)) => do
      v_4114 <- getRegister v_2483;
      v_4121 <- getRegister v_2484;
      setRegister (lhs.of_reg v_2485) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4114 64 128) 53 11) (MInt2Float (extract v_4114 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4121 64 128) 53 11) (MInt2Float (extract v_4121 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4114 192 256) 53 11) (MInt2Float (extract v_4114 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4121 192 256) 53 11) (MInt2Float (extract v_4121 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2466 : Mem) (v_2467 : reg (bv 128)) (v_2468 : reg (bv 128)) => do
      v_9557 <- evaluateAddress v_2466;
      v_9558 <- load v_9557 16;
      v_9565 <- getRegister v_2467;
      setRegister (lhs.of_reg v_2468) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9558 64 128) 53 11) (MInt2Float (extract v_9558 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9565 64 128) 53 11) (MInt2Float (extract v_9565 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 256)) (v_2479 : reg (bv 256)) => do
      v_9574 <- evaluateAddress v_2477;
      v_9575 <- load v_9574 32;
      v_9582 <- getRegister v_2478;
      setRegister (lhs.of_reg v_2479) (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9575 64 128) 53 11) (MInt2Float (extract v_9575 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9582 64 128) 53 11) (MInt2Float (extract v_9582 0 64) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9575 192 256) 53 11) (MInt2Float (extract v_9575 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9582 192 256) 53 11) (MInt2Float (extract v_9582 128 192) 53 11)) 64)));
      pure ()
    pat_end
