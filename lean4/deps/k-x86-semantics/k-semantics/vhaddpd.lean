def vhaddpd1 : instruction :=
  definst "vhaddpd" $ do
    pattern fun (v_3539 : reg (bv 128)) (v_3540 : reg (bv 128)) (v_3541 : reg (bv 128)) => do
      v_8147 <- getRegister v_3539;
      v_8154 <- getRegister v_3540;
      setRegister (lhs.of_reg v_3541) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8147 64 128) 53 11) (MInt2Float (extract v_8147 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8154 64 128) 53 11) (MInt2Float (extract v_8154 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3549 : reg (bv 256)) (v_3550 : reg (bv 256)) (v_3551 : reg (bv 256)) => do
      v_8168 <- getRegister v_3549;
      v_8175 <- getRegister v_3550;
      setRegister (lhs.of_reg v_3551) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8168 64 128) 53 11) (MInt2Float (extract v_8168 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8175 64 128) 53 11) (MInt2Float (extract v_8175 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8168 192 256) 53 11) (MInt2Float (extract v_8168 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8175 192 256) 53 11) (MInt2Float (extract v_8175 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3533 : Mem) (v_3534 : reg (bv 128)) (v_3535 : reg (bv 128)) => do
      v_13773 <- evaluateAddress v_3533;
      v_13774 <- load v_13773 16;
      v_13781 <- getRegister v_3534;
      setRegister (lhs.of_reg v_3535) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13774 64 128) 53 11) (MInt2Float (extract v_13774 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13781 64 128) 53 11) (MInt2Float (extract v_13781 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3544 : Mem) (v_3545 : reg (bv 256)) (v_3546 : reg (bv 256)) => do
      v_13790 <- evaluateAddress v_3544;
      v_13791 <- load v_13790 32;
      v_13798 <- getRegister v_3545;
      setRegister (lhs.of_reg v_3546) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13791 64 128) 53 11) (MInt2Float (extract v_13791 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13798 64 128) 53 11) (MInt2Float (extract v_13798 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13791 192 256) 53 11) (MInt2Float (extract v_13791 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13798 192 256) 53 11) (MInt2Float (extract v_13798 128 192) 53 11)) 64)));
      pure ()
    pat_end
