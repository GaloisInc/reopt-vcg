def hsubpd1 : instruction :=
  definst "hsubpd" $ do
    pattern fun (v_2897 : reg (bv 128)) (v_2898 : reg (bv 128)) => do
      v_4822 <- getRegister v_2897;
      v_4829 <- getRegister v_2898;
      setRegister (lhs.of_reg v_2898) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4822 64 128) 53 11) (MInt2Float (extract v_4822 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4829 64 128) 53 11) (MInt2Float (extract v_4829 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2892 : Mem) (v_2893 : reg (bv 128)) => do
      v_8297 <- evaluateAddress v_2892;
      v_8298 <- load v_8297 16;
      v_8305 <- getRegister v_2893;
      setRegister (lhs.of_reg v_2893) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8298 64 128) 53 11) (MInt2Float (extract v_8298 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8305 64 128) 53 11) (MInt2Float (extract v_8305 0 64) 53 11)) 64));
      pure ()
    pat_end
