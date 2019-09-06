def vaddpd1 : instruction :=
  definst "vaddpd" $ do
    pattern fun (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) (v_2663 : reg (bv 128)) => do
      v_4812 <- getRegister v_2662;
      v_4815 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2663) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4812 0 64) 53 11) (MInt2Float (extract v_4815 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4812 64 128) 53 11) (MInt2Float (extract v_4815 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2669 : reg (bv 256)) (v_2670 : reg (bv 256)) (v_2671 : reg (bv 256)) => do
      v_4833 <- getRegister v_2670;
      v_4836 <- getRegister v_2669;
      setRegister (lhs.of_reg v_2671) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4833 0 64) 53 11) (MInt2Float (extract v_4836 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4833 64 128) 53 11) (MInt2Float (extract v_4836 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4833 128 192) 53 11) (MInt2Float (extract v_4836 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4833 192 256) 53 11) (MInt2Float (extract v_4836 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2653 : Mem) (v_2656 : reg (bv 128)) (v_2657 : reg (bv 128)) => do
      v_9121 <- getRegister v_2656;
      v_9124 <- evaluateAddress v_2653;
      v_9125 <- load v_9124 16;
      setRegister (lhs.of_reg v_2657) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9121 0 64) 53 11) (MInt2Float (extract v_9125 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9121 64 128) 53 11) (MInt2Float (extract v_9125 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2664 : Mem) (v_2665 : reg (bv 256)) (v_2666 : reg (bv 256)) => do
      v_9138 <- getRegister v_2665;
      v_9141 <- evaluateAddress v_2664;
      v_9142 <- load v_9141 32;
      setRegister (lhs.of_reg v_2666) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9138 0 64) 53 11) (MInt2Float (extract v_9142 0 64) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9138 64 128) 53 11) (MInt2Float (extract v_9142 64 128) 53 11)) 64) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9138 128 192) 53 11) (MInt2Float (extract v_9142 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9138 192 256) 53 11) (MInt2Float (extract v_9142 192 256) 53 11)) 64))));
      pure ()
    pat_end
