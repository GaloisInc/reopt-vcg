def vaddsubpd1 : instruction :=
  definst "vaddsubpd" $ do
    pattern fun (v_2727 : reg (bv 128)) (v_2728 : reg (bv 128)) (v_2729 : reg (bv 128)) => do
      v_4998 <- getRegister v_2728;
      v_5001 <- getRegister v_2727;
      setRegister (lhs.of_reg v_2729) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4998 0 64) 53 11) (MInt2Float (extract v_5001 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4998 64 128) 53 11) (MInt2Float (extract v_5001 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2735 : reg (bv 256)) (v_2736 : reg (bv 256)) (v_2737 : reg (bv 256)) => do
      v_5019 <- getRegister v_2736;
      v_5022 <- getRegister v_2735;
      setRegister (lhs.of_reg v_2737) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5019 0 64) 53 11) (MInt2Float (extract v_5022 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5019 64 128) 53 11) (MInt2Float (extract v_5022 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_5019 128 192) 53 11) (MInt2Float (extract v_5022 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5019 192 256) 53 11) (MInt2Float (extract v_5022 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2719 : Mem) (v_2722 : reg (bv 128)) (v_2723 : reg (bv 128)) => do
      v_9281 <- getRegister v_2722;
      v_9284 <- evaluateAddress v_2719;
      v_9285 <- load v_9284 16;
      setRegister (lhs.of_reg v_2723) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9281 0 64) 53 11) (MInt2Float (extract v_9285 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9281 64 128) 53 11) (MInt2Float (extract v_9285 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2730 : Mem) (v_2731 : reg (bv 256)) (v_2732 : reg (bv 256)) => do
      v_9298 <- getRegister v_2731;
      v_9301 <- evaluateAddress v_2730;
      v_9302 <- load v_9301 32;
      setRegister (lhs.of_reg v_2732) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9298 0 64) 53 11) (MInt2Float (extract v_9302 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9298 64 128) 53 11) (MInt2Float (extract v_9302 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9298 128 192) 53 11) (MInt2Float (extract v_9302 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9298 192 256) 53 11) (MInt2Float (extract v_9302 192 256) 53 11)) 64)));
      pure ()
    pat_end
