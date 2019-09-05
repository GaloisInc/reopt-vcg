def vhaddps1 : instruction :=
  definst "vhaddps" $ do
    pattern fun (v_2449 : reg (bv 128)) (v_2450 : reg (bv 128)) (v_2451 : reg (bv 128)) => do
      v_3995 <- getRegister v_2449;
      v_4009 <- getRegister v_2450;
      setRegister (lhs.of_reg v_2451) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3995 32 64) 24 8) (MInt2Float (extract v_3995 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3995 96 128) 24 8) (MInt2Float (extract v_3995 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4009 32 64) 24 8) (MInt2Float (extract v_4009 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4009 96 128) 24 8) (MInt2Float (extract v_4009 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2461 : reg (bv 256)) (v_2462 : reg (bv 256)) (v_2463 : reg (bv 256)) => do
      v_4030 <- getRegister v_2461;
      v_4044 <- getRegister v_2462;
      setRegister (lhs.of_reg v_2463) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4030 32 64) 24 8) (MInt2Float (extract v_4030 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4030 96 128) 24 8) (MInt2Float (extract v_4030 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4044 32 64) 24 8) (MInt2Float (extract v_4044 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4044 96 128) 24 8) (MInt2Float (extract v_4044 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4030 160 192) 24 8) (MInt2Float (extract v_4030 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4030 224 256) 24 8) (MInt2Float (extract v_4030 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4044 160 192) 24 8) (MInt2Float (extract v_4044 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4044 224 256) 24 8) (MInt2Float (extract v_4044 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2444 : Mem) (v_2445 : reg (bv 128)) (v_2446 : reg (bv 128)) => do
      v_9467 <- evaluateAddress v_2444;
      v_9468 <- load v_9467 16;
      v_9482 <- getRegister v_2445;
      setRegister (lhs.of_reg v_2446) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9468 32 64) 24 8) (MInt2Float (extract v_9468 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9468 96 128) 24 8) (MInt2Float (extract v_9468 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9482 32 64) 24 8) (MInt2Float (extract v_9482 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9482 96 128) 24 8) (MInt2Float (extract v_9482 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2455 : Mem) (v_2456 : reg (bv 256)) (v_2457 : reg (bv 256)) => do
      v_9498 <- evaluateAddress v_2455;
      v_9499 <- load v_9498 32;
      v_9513 <- getRegister v_2456;
      setRegister (lhs.of_reg v_2457) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9499 32 64) 24 8) (MInt2Float (extract v_9499 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9499 96 128) 24 8) (MInt2Float (extract v_9499 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9513 32 64) 24 8) (MInt2Float (extract v_9513 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9513 96 128) 24 8) (MInt2Float (extract v_9513 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9499 160 192) 24 8) (MInt2Float (extract v_9499 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9499 224 256) 24 8) (MInt2Float (extract v_9499 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9513 160 192) 24 8) (MInt2Float (extract v_9513 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9513 224 256) 24 8) (MInt2Float (extract v_9513 192 224) 24 8)) 32)));
      pure ()
    pat_end
