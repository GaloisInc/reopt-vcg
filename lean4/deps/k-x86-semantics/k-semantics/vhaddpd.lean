def vhaddpd1 : instruction :=
  definst "vhaddpd" $ do
    pattern fun (v_3563 : reg (bv 128)) (v_3564 : reg (bv 128)) (v_3565 : reg (bv 128)) => do
      v_8174 <- getRegister v_3563;
      v_8181 <- getRegister v_3564;
      setRegister (lhs.of_reg v_3565) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8174 64 128) 53 11) (MInt2Float (extract v_8174 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8181 64 128) 53 11) (MInt2Float (extract v_8181 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3577 : reg (bv 256)) (v_3578 : reg (bv 256)) (v_3579 : reg (bv 256)) => do
      v_8195 <- getRegister v_3577;
      v_8202 <- getRegister v_3578;
      setRegister (lhs.of_reg v_3579) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8195 64 128) 53 11) (MInt2Float (extract v_8195 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8202 64 128) 53 11) (MInt2Float (extract v_8202 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8195 192 256) 53 11) (MInt2Float (extract v_8195 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8202 192 256) 53 11) (MInt2Float (extract v_8202 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3560 : Mem) (v_3558 : reg (bv 128)) (v_3559 : reg (bv 128)) => do
      v_13800 <- evaluateAddress v_3560;
      v_13801 <- load v_13800 16;
      v_13808 <- getRegister v_3558;
      setRegister (lhs.of_reg v_3559) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13801 64 128) 53 11) (MInt2Float (extract v_13801 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13808 64 128) 53 11) (MInt2Float (extract v_13808 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3569 : Mem) (v_3572 : reg (bv 256)) (v_3573 : reg (bv 256)) => do
      v_13817 <- evaluateAddress v_3569;
      v_13818 <- load v_13817 32;
      v_13825 <- getRegister v_3572;
      setRegister (lhs.of_reg v_3573) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13818 64 128) 53 11) (MInt2Float (extract v_13818 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13825 64 128) 53 11) (MInt2Float (extract v_13825 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13818 192 256) 53 11) (MInt2Float (extract v_13818 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13825 192 256) 53 11) (MInt2Float (extract v_13825 128 192) 53 11)) 64)));
      pure ()
    pat_end
