def vaddsubpd1 : instruction :=
  definst "vaddsubpd" $ do
    pattern fun (v_2636 : reg (bv 128)) (v_2637 : reg (bv 128)) (v_2638 : reg (bv 128)) => do
      v_4999 <- getRegister v_2637;
      v_5002 <- getRegister v_2636;
      setRegister (lhs.of_reg v_2638) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4999 0 64) 53 11) (MInt2Float (extract v_5002 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4999 64 128) 53 11) (MInt2Float (extract v_5002 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2645 : reg (bv 256)) (v_2646 : reg (bv 256)) (v_2647 : reg (bv 256)) => do
      v_5020 <- getRegister v_2646;
      v_5023 <- getRegister v_2645;
      setRegister (lhs.of_reg v_2647) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5020 0 64) 53 11) (MInt2Float (extract v_5023 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5020 64 128) 53 11) (MInt2Float (extract v_5023 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5020 128 192) 53 11) (MInt2Float (extract v_5023 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5020 192 256) 53 11) (MInt2Float (extract v_5023 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2628 : Mem) (v_2631 : reg (bv 128)) (v_2632 : reg (bv 128)) => do
      v_9442 <- getRegister v_2631;
      v_9445 <- evaluateAddress v_2628;
      v_9446 <- load v_9445 16;
      setRegister (lhs.of_reg v_2632) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9442 0 64) 53 11) (MInt2Float (extract v_9446 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9442 64 128) 53 11) (MInt2Float (extract v_9446 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2639 : Mem) (v_2640 : reg (bv 256)) (v_2641 : reg (bv 256)) => do
      v_9459 <- getRegister v_2640;
      v_9462 <- evaluateAddress v_2639;
      v_9463 <- load v_9462 32;
      setRegister (lhs.of_reg v_2641) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9459 0 64) 53 11) (MInt2Float (extract v_9463 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9459 64 128) 53 11) (MInt2Float (extract v_9463 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9459 128 192) 53 11) (MInt2Float (extract v_9463 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9459 192 256) 53 11) (MInt2Float (extract v_9463 192 256) 53 11)) 64)));
      pure ()
    pat_end
