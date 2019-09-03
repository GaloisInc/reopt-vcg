def vaddsubps1 : instruction :=
  definst "vaddsubps" $ do
    pattern fun (v_2658 : reg (bv 128)) (v_2659 : reg (bv 128)) (v_2660 : reg (bv 128)) => do
      v_5055 <- getRegister v_2659;
      v_5058 <- getRegister v_2658;
      setRegister (lhs.of_reg v_2660) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5055 0 32) 24 8) (MInt2Float (extract v_5058 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5055 32 64) 24 8) (MInt2Float (extract v_5058 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5055 64 96) 24 8) (MInt2Float (extract v_5058 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5055 96 128) 24 8) (MInt2Float (extract v_5058 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2667 : reg (bv 256)) (v_2668 : reg (bv 256)) (v_2669 : reg (bv 256)) => do
      v_5090 <- getRegister v_2668;
      v_5093 <- getRegister v_2667;
      setRegister (lhs.of_reg v_2669) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5090 0 32) 24 8) (MInt2Float (extract v_5093 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5090 32 64) 24 8) (MInt2Float (extract v_5093 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5090 64 96) 24 8) (MInt2Float (extract v_5093 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5090 96 128) 24 8) (MInt2Float (extract v_5093 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5090 128 160) 24 8) (MInt2Float (extract v_5093 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5090 160 192) 24 8) (MInt2Float (extract v_5093 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5090 192 224) 24 8) (MInt2Float (extract v_5093 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5090 224 256) 24 8) (MInt2Float (extract v_5093 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2653 : reg (bv 128)) (v_2654 : reg (bv 128)) => do
      v_9490 <- getRegister v_2653;
      v_9493 <- evaluateAddress v_2650;
      v_9494 <- load v_9493 16;
      setRegister (lhs.of_reg v_2654) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9490 0 32) 24 8) (MInt2Float (extract v_9494 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9490 32 64) 24 8) (MInt2Float (extract v_9494 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9490 64 96) 24 8) (MInt2Float (extract v_9494 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9490 96 128) 24 8) (MInt2Float (extract v_9494 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2661 : Mem) (v_2662 : reg (bv 256)) (v_2663 : reg (bv 256)) => do
      v_9521 <- getRegister v_2662;
      v_9524 <- evaluateAddress v_2661;
      v_9525 <- load v_9524 32;
      setRegister (lhs.of_reg v_2663) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9521 0 32) 24 8) (MInt2Float (extract v_9525 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9521 32 64) 24 8) (MInt2Float (extract v_9525 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9521 64 96) 24 8) (MInt2Float (extract v_9525 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9521 96 128) 24 8) (MInt2Float (extract v_9525 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9521 128 160) 24 8) (MInt2Float (extract v_9525 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9521 160 192) 24 8) (MInt2Float (extract v_9525 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9521 192 224) 24 8) (MInt2Float (extract v_9525 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9521 224 256) 24 8) (MInt2Float (extract v_9525 224 256) 24 8)) 32)))));
      pure ()
    pat_end
