def vhsubps1 : instruction :=
  definst "vhsubps" $ do
    pattern fun (v_2493 : reg (bv 128)) (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) => do
      v_4149 <- getRegister v_2493;
      v_4163 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2495) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4149 32 64) 24 8) (MInt2Float (extract v_4149 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4149 96 128) 24 8) (MInt2Float (extract v_4149 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4163 32 64) 24 8) (MInt2Float (extract v_4163 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4163 96 128) 24 8) (MInt2Float (extract v_4163 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) (v_2507 : reg (bv 256)) => do
      v_4184 <- getRegister v_2505;
      v_4198 <- getRegister v_2506;
      setRegister (lhs.of_reg v_2507) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4184 32 64) 24 8) (MInt2Float (extract v_4184 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4184 96 128) 24 8) (MInt2Float (extract v_4184 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4198 32 64) 24 8) (MInt2Float (extract v_4198 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4198 96 128) 24 8) (MInt2Float (extract v_4198 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4184 160 192) 24 8) (MInt2Float (extract v_4184 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4184 224 256) 24 8) (MInt2Float (extract v_4184 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4198 160 192) 24 8) (MInt2Float (extract v_4198 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4198 224 256) 24 8) (MInt2Float (extract v_4198 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2489 : reg (bv 128)) (v_2490 : reg (bv 128)) => do
      v_9605 <- evaluateAddress v_2488;
      v_9606 <- load v_9605 16;
      v_9620 <- getRegister v_2489;
      setRegister (lhs.of_reg v_2490) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9606 32 64) 24 8) (MInt2Float (extract v_9606 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9606 96 128) 24 8) (MInt2Float (extract v_9606 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9620 32 64) 24 8) (MInt2Float (extract v_9620 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9620 96 128) 24 8) (MInt2Float (extract v_9620 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2499 : Mem) (v_2500 : reg (bv 256)) (v_2501 : reg (bv 256)) => do
      v_9636 <- evaluateAddress v_2499;
      v_9637 <- load v_9636 32;
      v_9651 <- getRegister v_2500;
      setRegister (lhs.of_reg v_2501) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9637 32 64) 24 8) (MInt2Float (extract v_9637 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9637 96 128) 24 8) (MInt2Float (extract v_9637 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9651 32 64) 24 8) (MInt2Float (extract v_9651 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9651 96 128) 24 8) (MInt2Float (extract v_9651 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9637 160 192) 24 8) (MInt2Float (extract v_9637 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9637 224 256) 24 8) (MInt2Float (extract v_9637 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9651 160 192) 24 8) (MInt2Float (extract v_9651 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9651 224 256) 24 8) (MInt2Float (extract v_9651 192 224) 24 8)) 32)));
      pure ()
    pat_end
