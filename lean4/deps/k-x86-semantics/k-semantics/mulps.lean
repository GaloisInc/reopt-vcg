def mulps1 : instruction :=
  definst "mulps" $ do
    pattern fun (v_2825 : reg (bv 128)) (v_2826 : reg (bv 128)) => do
      v_4272 <- getRegister v_2826;
      v_4275 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2826) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4272 0 32) 24 8) (MInt2Float (extract v_4275 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4272 32 64) 24 8) (MInt2Float (extract v_4275 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4272 64 96) 24 8) (MInt2Float (extract v_4275 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4272 96 128) 24 8) (MInt2Float (extract v_4275 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2821 : Mem) (v_2822 : reg (bv 128)) => do
      v_8840 <- getRegister v_2822;
      v_8843 <- evaluateAddress v_2821;
      v_8844 <- load v_8843 16;
      setRegister (lhs.of_reg v_2822) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8840 0 32) 24 8) (MInt2Float (extract v_8844 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8840 32 64) 24 8) (MInt2Float (extract v_8844 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8840 64 96) 24 8) (MInt2Float (extract v_8844 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8840 96 128) 24 8) (MInt2Float (extract v_8844 96 128) 24 8)) 32))));
      pure ()
    pat_end
