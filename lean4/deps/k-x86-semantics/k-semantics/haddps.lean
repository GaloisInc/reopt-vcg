def haddps1 : instruction :=
  definst "haddps" $ do
    pattern fun (v_2914 : reg (bv 128)) (v_2915 : reg (bv 128)) => do
      v_4809 <- getRegister v_2914;
      v_4823 <- getRegister v_2915;
      setRegister (lhs.of_reg v_2915) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4809 32 64) 24 8) (MInt2Float (extract v_4809 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4809 96 128) 24 8) (MInt2Float (extract v_4809 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4823 32 64) 24 8) (MInt2Float (extract v_4823 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4823 96 128) 24 8) (MInt2Float (extract v_4823 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2911 : reg (bv 128)) => do
      v_8276 <- evaluateAddress v_2910;
      v_8277 <- load v_8276 16;
      v_8291 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2911) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8277 32 64) 24 8) (MInt2Float (extract v_8277 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8277 96 128) 24 8) (MInt2Float (extract v_8277 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8291 32 64) 24 8) (MInt2Float (extract v_8291 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8291 96 128) 24 8) (MInt2Float (extract v_8291 64 96) 24 8)) 32));
      pure ()
    pat_end
