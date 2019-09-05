def mulsd1 : instruction :=
  definst "mulsd" $ do
    pattern fun (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_4299 <- getRegister v_2817;
      v_4303 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2817) (concat (extract v_4299 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4299 64 128) 53 11) (MInt2Float (extract v_4303 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2812 : reg (bv 128)) => do
      v_8862 <- getRegister v_2812;
      v_8866 <- evaluateAddress v_2811;
      v_8867 <- load v_8866 8;
      setRegister (lhs.of_reg v_2812) (concat (extract v_8862 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8862 64 128) 53 11) (MInt2Float v_8867 53 11)) 64));
      pure ()
    pat_end
