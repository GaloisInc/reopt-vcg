def vaddsubps1 : instruction :=
  definst "vaddsubps" $ do
    pattern fun (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) (v_2751 : reg (bv 128)) => do
      v_5054 <- getRegister v_2750;
      v_5057 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2751) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5054 0 32) 24 8) (MInt2Float (extract v_5057 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5054 32 64) 24 8) (MInt2Float (extract v_5057 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5054 64 96) 24 8) (MInt2Float (extract v_5057 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5054 96 128) 24 8) (MInt2Float (extract v_5057 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2757 : reg (bv 256)) (v_2758 : reg (bv 256)) (v_2759 : reg (bv 256)) => do
      v_5089 <- getRegister v_2758;
      v_5092 <- getRegister v_2757;
      setRegister (lhs.of_reg v_2759) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5089 0 32) 24 8) (MInt2Float (extract v_5092 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5089 32 64) 24 8) (MInt2Float (extract v_5092 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5089 64 96) 24 8) (MInt2Float (extract v_5092 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5089 96 128) 24 8) (MInt2Float (extract v_5092 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5089 128 160) 24 8) (MInt2Float (extract v_5092 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5089 160 192) 24 8) (MInt2Float (extract v_5092 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5089 192 224) 24 8) (MInt2Float (extract v_5092 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5089 224 256) 24 8) (MInt2Float (extract v_5092 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) (v_2744 : reg (bv 128)) (v_2745 : reg (bv 128)) => do
      v_9329 <- getRegister v_2744;
      v_9332 <- evaluateAddress v_2741;
      v_9333 <- load v_9332 16;
      setRegister (lhs.of_reg v_2745) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9329 0 32) 24 8) (MInt2Float (extract v_9333 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9329 32 64) 24 8) (MInt2Float (extract v_9333 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9329 64 96) 24 8) (MInt2Float (extract v_9333 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9329 96 128) 24 8) (MInt2Float (extract v_9333 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2752 : Mem) (v_2753 : reg (bv 256)) (v_2754 : reg (bv 256)) => do
      v_9360 <- getRegister v_2753;
      v_9363 <- evaluateAddress v_2752;
      v_9364 <- load v_9363 32;
      setRegister (lhs.of_reg v_2754) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9360 0 32) 24 8) (MInt2Float (extract v_9364 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9360 32 64) 24 8) (MInt2Float (extract v_9364 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9360 64 96) 24 8) (MInt2Float (extract v_9364 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9360 96 128) 24 8) (MInt2Float (extract v_9364 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9360 128 160) 24 8) (MInt2Float (extract v_9364 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9360 160 192) 24 8) (MInt2Float (extract v_9364 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9360 192 224) 24 8) (MInt2Float (extract v_9364 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9360 224 256) 24 8) (MInt2Float (extract v_9364 224 256) 24 8)) 32)))));
      pure ()
    pat_end
