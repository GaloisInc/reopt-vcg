def vhaddps1 : instruction :=
  definst "vhaddps" $ do
    pattern fun (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) (v_2476 : reg (bv 128)) => do
      v_4022 <- getRegister v_2474;
      v_4036 <- getRegister v_2475;
      setRegister (lhs.of_reg v_2476) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4022 32 64) 24 8) (MInt2Float (extract v_4022 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4022 96 128) 24 8) (MInt2Float (extract v_4022 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4036 32 64) 24 8) (MInt2Float (extract v_4036 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4036 96 128) 24 8) (MInt2Float (extract v_4036 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2485 : reg (bv 256)) (v_2486 : reg (bv 256)) (v_2487 : reg (bv 256)) => do
      v_4057 <- getRegister v_2485;
      v_4071 <- getRegister v_2486;
      setRegister (lhs.of_reg v_2487) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4057 32 64) 24 8) (MInt2Float (extract v_4057 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4057 96 128) 24 8) (MInt2Float (extract v_4057 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4071 32 64) 24 8) (MInt2Float (extract v_4071 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4071 96 128) 24 8) (MInt2Float (extract v_4071 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4057 160 192) 24 8) (MInt2Float (extract v_4057 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4057 224 256) 24 8) (MInt2Float (extract v_4057 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4071 160 192) 24 8) (MInt2Float (extract v_4071 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4071 224 256) 24 8) (MInt2Float (extract v_4071 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2469 : Mem) (v_2470 : reg (bv 128)) (v_2471 : reg (bv 128)) => do
      v_9494 <- evaluateAddress v_2469;
      v_9495 <- load v_9494 16;
      v_9509 <- getRegister v_2470;
      setRegister (lhs.of_reg v_2471) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9495 32 64) 24 8) (MInt2Float (extract v_9495 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9495 96 128) 24 8) (MInt2Float (extract v_9495 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9509 32 64) 24 8) (MInt2Float (extract v_9509 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9509 96 128) 24 8) (MInt2Float (extract v_9509 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2480 : Mem) (v_2481 : reg (bv 256)) (v_2482 : reg (bv 256)) => do
      v_9525 <- evaluateAddress v_2480;
      v_9526 <- load v_9525 32;
      v_9540 <- getRegister v_2481;
      setRegister (lhs.of_reg v_2482) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9526 32 64) 24 8) (MInt2Float (extract v_9526 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9526 96 128) 24 8) (MInt2Float (extract v_9526 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9540 32 64) 24 8) (MInt2Float (extract v_9540 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9540 96 128) 24 8) (MInt2Float (extract v_9540 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9526 160 192) 24 8) (MInt2Float (extract v_9526 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9526 224 256) 24 8) (MInt2Float (extract v_9526 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9540 160 192) 24 8) (MInt2Float (extract v_9540 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9540 224 256) 24 8) (MInt2Float (extract v_9540 192 224) 24 8)) 32)));
      pure ()
    pat_end
