def vaddsubpd1 : instruction :=
  definst "vaddsubpd" $ do
    pattern fun (v_2700 : reg (bv 128)) (v_2701 : reg (bv 128)) (v_2702 : reg (bv 128)) => do
      v_4971 <- getRegister v_2701;
      v_4974 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2702) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4971 0 64) 53 11) (MInt2Float (extract v_4974 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4971 64 128) 53 11) (MInt2Float (extract v_4974 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2710 : reg (bv 256)) (v_2711 : reg (bv 256)) (v_2712 : reg (bv 256)) => do
      v_4992 <- getRegister v_2711;
      v_4995 <- getRegister v_2710;
      setRegister (lhs.of_reg v_2712) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4992 0 64) 53 11) (MInt2Float (extract v_4995 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4992 64 128) 53 11) (MInt2Float (extract v_4995 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4992 128 192) 53 11) (MInt2Float (extract v_4995 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4992 192 256) 53 11) (MInt2Float (extract v_4995 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2694 : Mem) (v_2695 : reg (bv 128)) (v_2696 : reg (bv 128)) => do
      v_9254 <- getRegister v_2695;
      v_9257 <- evaluateAddress v_2694;
      v_9258 <- load v_9257 16;
      setRegister (lhs.of_reg v_2696) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9254 0 64) 53 11) (MInt2Float (extract v_9258 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9254 64 128) 53 11) (MInt2Float (extract v_9258 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2705 : Mem) (v_2706 : reg (bv 256)) (v_2707 : reg (bv 256)) => do
      v_9271 <- getRegister v_2706;
      v_9274 <- evaluateAddress v_2705;
      v_9275 <- load v_9274 32;
      setRegister (lhs.of_reg v_2707) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9271 0 64) 53 11) (MInt2Float (extract v_9275 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9271 64 128) 53 11) (MInt2Float (extract v_9275 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9271 128 192) 53 11) (MInt2Float (extract v_9275 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9271 192 256) 53 11) (MInt2Float (extract v_9275 192 256) 53 11)) 64)));
      pure ()
    pat_end
