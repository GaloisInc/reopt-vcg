def vaddsubps1 : instruction :=
  definst "vaddsubps" $ do
    pattern fun (v_2722 : reg (bv 128)) (v_2723 : reg (bv 128)) (v_2724 : reg (bv 128)) => do
      v_5027 <- getRegister v_2723;
      v_5030 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2724) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5027 0 32) 24 8) (MInt2Float (extract v_5030 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5027 32 64) 24 8) (MInt2Float (extract v_5030 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5027 64 96) 24 8) (MInt2Float (extract v_5030 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5027 96 128) 24 8) (MInt2Float (extract v_5030 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2732 : reg (bv 256)) (v_2733 : reg (bv 256)) (v_2734 : reg (bv 256)) => do
      v_5062 <- getRegister v_2733;
      v_5065 <- getRegister v_2732;
      setRegister (lhs.of_reg v_2734) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5062 0 32) 24 8) (MInt2Float (extract v_5065 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5062 32 64) 24 8) (MInt2Float (extract v_5065 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5062 64 96) 24 8) (MInt2Float (extract v_5065 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5062 96 128) 24 8) (MInt2Float (extract v_5065 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5062 128 160) 24 8) (MInt2Float (extract v_5065 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5062 160 192) 24 8) (MInt2Float (extract v_5065 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5062 192 224) 24 8) (MInt2Float (extract v_5065 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5062 224 256) 24 8) (MInt2Float (extract v_5065 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2716 : Mem) (v_2717 : reg (bv 128)) (v_2718 : reg (bv 128)) => do
      v_9302 <- getRegister v_2717;
      v_9305 <- evaluateAddress v_2716;
      v_9306 <- load v_9305 16;
      setRegister (lhs.of_reg v_2718) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9302 0 32) 24 8) (MInt2Float (extract v_9306 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9302 32 64) 24 8) (MInt2Float (extract v_9306 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9302 64 96) 24 8) (MInt2Float (extract v_9306 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9302 96 128) 24 8) (MInt2Float (extract v_9306 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2727 : Mem) (v_2728 : reg (bv 256)) (v_2729 : reg (bv 256)) => do
      v_9333 <- getRegister v_2728;
      v_9336 <- evaluateAddress v_2727;
      v_9337 <- load v_9336 32;
      setRegister (lhs.of_reg v_2729) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9333 0 32) 24 8) (MInt2Float (extract v_9337 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9333 32 64) 24 8) (MInt2Float (extract v_9337 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9333 64 96) 24 8) (MInt2Float (extract v_9337 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9333 96 128) 24 8) (MInt2Float (extract v_9337 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9333 128 160) 24 8) (MInt2Float (extract v_9337 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9333 160 192) 24 8) (MInt2Float (extract v_9337 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9333 192 224) 24 8) (MInt2Float (extract v_9337 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9333 224 256) 24 8) (MInt2Float (extract v_9337 224 256) 24 8)) 32)))));
      pure ()
    pat_end
