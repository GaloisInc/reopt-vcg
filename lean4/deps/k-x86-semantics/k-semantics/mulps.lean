def mulps1 : instruction :=
  definst "mulps" $ do
    pattern fun (v_2737 : reg (bv 128)) (v_2738 : reg (bv 128)) => do
      v_4184 <- getRegister v_2738;
      v_4187 <- getRegister v_2737;
      setRegister (lhs.of_reg v_2738) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4184 0 32) 24 8) (MInt2Float (extract v_4187 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4184 32 64) 24 8) (MInt2Float (extract v_4187 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4184 64 96) 24 8) (MInt2Float (extract v_4187 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4184 96 128) 24 8) (MInt2Float (extract v_4187 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 128)) => do
      v_8972 <- getRegister v_2733;
      v_8975 <- evaluateAddress v_2732;
      v_8976 <- load v_8975 16;
      setRegister (lhs.of_reg v_2733) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8972 0 32) 24 8) (MInt2Float (extract v_8976 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8972 32 64) 24 8) (MInt2Float (extract v_8976 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8972 64 96) 24 8) (MInt2Float (extract v_8976 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8972 96 128) 24 8) (MInt2Float (extract v_8976 96 128) 24 8)) 32))));
      pure ()
    pat_end
