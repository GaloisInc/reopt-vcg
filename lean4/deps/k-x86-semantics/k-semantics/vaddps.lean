def vaddps1 : instruction :=
  definst "vaddps" $ do
    pattern fun (v_2592 : reg (bv 128)) (v_2593 : reg (bv 128)) (v_2594 : reg (bv 128)) => do
      v_4869 <- getRegister v_2593;
      v_4872 <- getRegister v_2592;
      setRegister (lhs.of_reg v_2594) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4869 0 32) 24 8) (MInt2Float (extract v_4872 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4869 32 64) 24 8) (MInt2Float (extract v_4872 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4869 64 96) 24 8) (MInt2Float (extract v_4872 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4869 96 128) 24 8) (MInt2Float (extract v_4872 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2601 : reg (bv 256)) (v_2602 : reg (bv 256)) (v_2603 : reg (bv 256)) => do
      v_4904 <- getRegister v_2602;
      v_4907 <- getRegister v_2601;
      setRegister (lhs.of_reg v_2603) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 0 32) 24 8) (MInt2Float (extract v_4907 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 32 64) 24 8) (MInt2Float (extract v_4907 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 64 96) 24 8) (MInt2Float (extract v_4907 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 96 128) 24 8) (MInt2Float (extract v_4907 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 128 160) 24 8) (MInt2Float (extract v_4907 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 160 192) 24 8) (MInt2Float (extract v_4907 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 192 224) 24 8) (MInt2Float (extract v_4907 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4904 224 256) 24 8) (MInt2Float (extract v_4907 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2584 : Mem) (v_2587 : reg (bv 128)) (v_2588 : reg (bv 128)) => do
      v_9330 <- getRegister v_2587;
      v_9333 <- evaluateAddress v_2584;
      v_9334 <- load v_9333 16;
      setRegister (lhs.of_reg v_2588) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9330 0 32) 24 8) (MInt2Float (extract v_9334 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9330 32 64) 24 8) (MInt2Float (extract v_9334 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9330 64 96) 24 8) (MInt2Float (extract v_9334 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9330 96 128) 24 8) (MInt2Float (extract v_9334 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2595 : Mem) (v_2596 : reg (bv 256)) (v_2597 : reg (bv 256)) => do
      v_9361 <- getRegister v_2596;
      v_9364 <- evaluateAddress v_2595;
      v_9365 <- load v_9364 32;
      setRegister (lhs.of_reg v_2597) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 0 32) 24 8) (MInt2Float (extract v_9365 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 32 64) 24 8) (MInt2Float (extract v_9365 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 64 96) 24 8) (MInt2Float (extract v_9365 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 96 128) 24 8) (MInt2Float (extract v_9365 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 128 160) 24 8) (MInt2Float (extract v_9365 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 160 192) 24 8) (MInt2Float (extract v_9365 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 192 224) 24 8) (MInt2Float (extract v_9365 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9361 224 256) 24 8) (MInt2Float (extract v_9365 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
