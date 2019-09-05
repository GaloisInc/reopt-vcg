def haddpd1 : instruction :=
  definst "haddpd" $ do
    pattern fun (v_2879 : reg (bv 128)) (v_2880 : reg (bv 128)) => do
      v_4768 <- getRegister v_2879;
      v_4775 <- getRegister v_2880;
      setRegister (lhs.of_reg v_2880) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4768 64 128) 53 11) (MInt2Float (extract v_4768 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4775 64 128) 53 11) (MInt2Float (extract v_4775 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2874 : Mem) (v_2875 : reg (bv 128)) => do
      v_8249 <- evaluateAddress v_2874;
      v_8250 <- load v_8249 16;
      v_8257 <- getRegister v_2875;
      setRegister (lhs.of_reg v_2875) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8250 64 128) 53 11) (MInt2Float (extract v_8250 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8257 64 128) 53 11) (MInt2Float (extract v_8257 0 64) 53 11)) 64));
      pure ()
    pat_end
