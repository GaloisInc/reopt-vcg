def vhsubps1 : instruction :=
  definst "vhsubps" $ do
    pattern fun (v_2518 : reg (bv 128)) (v_2519 : reg (bv 128)) (v_2520 : reg (bv 128)) => do
      v_4176 <- getRegister v_2518;
      v_4190 <- getRegister v_2519;
      setRegister (lhs.of_reg v_2520) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4176 32 64) 24 8) (MInt2Float (extract v_4176 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4176 96 128) 24 8) (MInt2Float (extract v_4176 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4190 32 64) 24 8) (MInt2Float (extract v_4190 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4190 96 128) 24 8) (MInt2Float (extract v_4190 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2529 : reg (bv 256)) (v_2530 : reg (bv 256)) (v_2531 : reg (bv 256)) => do
      v_4211 <- getRegister v_2529;
      v_4225 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2531) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4211 32 64) 24 8) (MInt2Float (extract v_4211 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4211 96 128) 24 8) (MInt2Float (extract v_4211 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4225 32 64) 24 8) (MInt2Float (extract v_4225 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4225 96 128) 24 8) (MInt2Float (extract v_4225 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4211 160 192) 24 8) (MInt2Float (extract v_4211 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4211 224 256) 24 8) (MInt2Float (extract v_4211 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4225 160 192) 24 8) (MInt2Float (extract v_4225 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4225 224 256) 24 8) (MInt2Float (extract v_4225 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2513 : Mem) (v_2514 : reg (bv 128)) (v_2515 : reg (bv 128)) => do
      v_9632 <- evaluateAddress v_2513;
      v_9633 <- load v_9632 16;
      v_9647 <- getRegister v_2514;
      setRegister (lhs.of_reg v_2515) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9633 32 64) 24 8) (MInt2Float (extract v_9633 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9633 96 128) 24 8) (MInt2Float (extract v_9633 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9647 32 64) 24 8) (MInt2Float (extract v_9647 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9647 96 128) 24 8) (MInt2Float (extract v_9647 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2524 : Mem) (v_2525 : reg (bv 256)) (v_2526 : reg (bv 256)) => do
      v_9663 <- evaluateAddress v_2524;
      v_9664 <- load v_9663 32;
      v_9678 <- getRegister v_2525;
      setRegister (lhs.of_reg v_2526) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9664 32 64) 24 8) (MInt2Float (extract v_9664 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9664 96 128) 24 8) (MInt2Float (extract v_9664 64 96) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9678 32 64) 24 8) (MInt2Float (extract v_9678 0 32) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9678 96 128) 24 8) (MInt2Float (extract v_9678 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9664 160 192) 24 8) (MInt2Float (extract v_9664 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9664 224 256) 24 8) (MInt2Float (extract v_9664 192 224) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9678 160 192) 24 8) (MInt2Float (extract v_9678 128 160) 24 8)) 32)) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9678 224 256) 24 8) (MInt2Float (extract v_9678 192 224) 24 8)) 32)));
      pure ()
    pat_end
