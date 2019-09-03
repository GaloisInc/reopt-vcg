def vaddpd1 : instruction :=
  definst "vaddpd" $ do
    pattern fun (v_2570 : reg (bv 128)) (v_2571 : reg (bv 128)) (v_2572 : reg (bv 128)) => do
      v_4813 <- getRegister v_2571;
      v_4816 <- getRegister v_2570;
      setRegister (lhs.of_reg v_2572) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4813 0 64) 53 11) (MInt2Float (extract v_4816 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4813 64 128) 53 11) (MInt2Float (extract v_4816 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2579 : reg (bv 256)) (v_2580 : reg (bv 256)) (v_2581 : reg (bv 256)) => do
      v_4834 <- getRegister v_2580;
      v_4837 <- getRegister v_2579;
      setRegister (lhs.of_reg v_2581) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4834 0 64) 53 11) (MInt2Float (extract v_4837 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4834 64 128) 53 11) (MInt2Float (extract v_4837 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4834 128 192) 53 11) (MInt2Float (extract v_4837 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4834 192 256) 53 11) (MInt2Float (extract v_4837 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2562 : Mem) (v_2565 : reg (bv 128)) (v_2566 : reg (bv 128)) => do
      v_9282 <- getRegister v_2565;
      v_9285 <- evaluateAddress v_2562;
      v_9286 <- load v_9285 16;
      setRegister (lhs.of_reg v_2566) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9282 0 64) 53 11) (MInt2Float (extract v_9286 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9282 64 128) 53 11) (MInt2Float (extract v_9286 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2573 : Mem) (v_2574 : reg (bv 256)) (v_2575 : reg (bv 256)) => do
      v_9299 <- getRegister v_2574;
      v_9302 <- evaluateAddress v_2573;
      v_9303 <- load v_9302 32;
      setRegister (lhs.of_reg v_2575) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9299 0 64) 53 11) (MInt2Float (extract v_9303 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9299 64 128) 53 11) (MInt2Float (extract v_9303 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9299 128 192) 53 11) (MInt2Float (extract v_9303 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9299 192 256) 53 11) (MInt2Float (extract v_9303 192 256) 53 11)) 64))));
      pure ()
    pat_end
