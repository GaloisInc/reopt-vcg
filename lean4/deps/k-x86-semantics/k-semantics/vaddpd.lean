def vaddpd1 : instruction :=
  definst "vaddpd" $ do
    pattern fun (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) (v_2636 : reg (bv 128)) => do
      v_4785 <- getRegister v_2635;
      v_4788 <- getRegister v_2634;
      setRegister (lhs.of_reg v_2636) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4785 0 64) 53 11) (MInt2Float (extract v_4788 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4785 64 128) 53 11) (MInt2Float (extract v_4788 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2644 : reg (bv 256)) (v_2645 : reg (bv 256)) (v_2646 : reg (bv 256)) => do
      v_4806 <- getRegister v_2645;
      v_4809 <- getRegister v_2644;
      setRegister (lhs.of_reg v_2646) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4806 0 64) 53 11) (MInt2Float (extract v_4809 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4806 64 128) 53 11) (MInt2Float (extract v_4809 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4806 128 192) 53 11) (MInt2Float (extract v_4809 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4806 192 256) 53 11) (MInt2Float (extract v_4809 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2628 : Mem) (v_2629 : reg (bv 128)) (v_2630 : reg (bv 128)) => do
      v_9094 <- getRegister v_2629;
      v_9097 <- evaluateAddress v_2628;
      v_9098 <- load v_9097 16;
      setRegister (lhs.of_reg v_2630) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9094 0 64) 53 11) (MInt2Float (extract v_9098 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9094 64 128) 53 11) (MInt2Float (extract v_9098 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2639 : Mem) (v_2640 : reg (bv 256)) (v_2641 : reg (bv 256)) => do
      v_9111 <- getRegister v_2640;
      v_9114 <- evaluateAddress v_2639;
      v_9115 <- load v_9114 32;
      setRegister (lhs.of_reg v_2641) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9111 0 64) 53 11) (MInt2Float (extract v_9115 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9111 64 128) 53 11) (MInt2Float (extract v_9115 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9111 128 192) 53 11) (MInt2Float (extract v_9115 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9111 192 256) 53 11) (MInt2Float (extract v_9115 192 256) 53 11)) 64))));
      pure ()
    pat_end
