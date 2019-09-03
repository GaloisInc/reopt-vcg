def vhsubps1 : instruction :=
  definst "vhsubps" $ do
    pattern fun (v_2430 : reg (bv 128)) (v_2431 : reg (bv 128)) (v_2432 : reg (bv 128)) => do
      v_4085 <- getRegister v_2430;
      v_4099 <- getRegister v_2431;
      setRegister (lhs.of_reg v_2432) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4085 32 64) 24 8) (MInt2Float (extract v_4085 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4085 96 128) 24 8) (MInt2Float (extract v_4085 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4099 32 64) 24 8) (MInt2Float (extract v_4099 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4099 96 128) 24 8) (MInt2Float (extract v_4099 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2441 : reg (bv 256)) (v_2442 : reg (bv 256)) (v_2443 : reg (bv 256)) => do
      v_4120 <- getRegister v_2441;
      v_4134 <- getRegister v_2442;
      setRegister (lhs.of_reg v_2443) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4120 32 64) 24 8) (MInt2Float (extract v_4120 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4120 96 128) 24 8) (MInt2Float (extract v_4120 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4134 32 64) 24 8) (MInt2Float (extract v_4134 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4134 96 128) 24 8) (MInt2Float (extract v_4134 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4120 160 192) 24 8) (MInt2Float (extract v_4120 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4120 224 256) 24 8) (MInt2Float (extract v_4120 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4134 160 192) 24 8) (MInt2Float (extract v_4134 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4134 224 256) 24 8) (MInt2Float (extract v_4134 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2425 : reg (bv 128)) (v_2426 : reg (bv 128)) => do
      v_9715 <- evaluateAddress v_2424;
      v_9716 <- load v_9715 16;
      v_9730 <- getRegister v_2425;
      setRegister (lhs.of_reg v_2426) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9716 32 64) 24 8) (MInt2Float (extract v_9716 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9716 96 128) 24 8) (MInt2Float (extract v_9716 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9730 32 64) 24 8) (MInt2Float (extract v_9730 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9730 96 128) 24 8) (MInt2Float (extract v_9730 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2435 : Mem) (v_2436 : reg (bv 256)) (v_2437 : reg (bv 256)) => do
      v_9746 <- evaluateAddress v_2435;
      v_9747 <- load v_9746 32;
      v_9761 <- getRegister v_2436;
      setRegister (lhs.of_reg v_2437) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9747 32 64) 24 8) (MInt2Float (extract v_9747 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9747 96 128) 24 8) (MInt2Float (extract v_9747 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9761 32 64) 24 8) (MInt2Float (extract v_9761 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9761 96 128) 24 8) (MInt2Float (extract v_9761 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9747 160 192) 24 8) (MInt2Float (extract v_9747 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9747 224 256) 24 8) (MInt2Float (extract v_9747 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9761 160 192) 24 8) (MInt2Float (extract v_9761 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9761 224 256) 24 8) (MInt2Float (extract v_9761 192 224) 24 8)) 32)));
      pure ()
    pat_end
