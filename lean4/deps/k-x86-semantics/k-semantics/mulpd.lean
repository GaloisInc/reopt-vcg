def mulpd1 : instruction :=
  definst "mulpd" $ do
    pattern fun (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_4252 <- getRegister v_2817;
      v_4255 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2817) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4252 0 64) 53 11) (MInt2Float (extract v_4255 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4252 64 128) 53 11) (MInt2Float (extract v_4255 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2812 : Mem) (v_2813 : reg (bv 128)) => do
      v_8823 <- getRegister v_2813;
      v_8826 <- evaluateAddress v_2812;
      v_8827 <- load v_8826 16;
      setRegister (lhs.of_reg v_2813) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8823 0 64) 53 11) (MInt2Float (extract v_8827 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8823 64 128) 53 11) (MInt2Float (extract v_8827 64 128) 53 11)) 64));
      pure ()
    pat_end
