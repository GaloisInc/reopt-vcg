def vaddsd1 : instruction :=
  definst "vaddsd" $ do
    pattern fun (v_2614 : reg (bv 128)) (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_4967 <- getRegister v_2615;
      v_4971 <- getRegister v_2614;
      setRegister (lhs.of_reg v_2616) (concat (extract v_4967 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4967 64 128) 53 11) (MInt2Float (extract v_4971 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2606 : Mem) (v_2609 : reg (bv 128)) (v_2610 : reg (bv 128)) => do
      v_9420 <- getRegister v_2609;
      v_9424 <- evaluateAddress v_2606;
      v_9425 <- load v_9424 8;
      setRegister (lhs.of_reg v_2610) (concat (extract v_9420 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9420 64 128) 53 11) (MInt2Float v_9425 53 11)) 64));
      pure ()
    pat_end
