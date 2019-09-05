def mulps1 : instruction :=
  definst "mulps" $ do
    pattern fun (v_2800 : reg (bv 128)) (v_2801 : reg (bv 128)) => do
      v_4245 <- getRegister v_2801;
      v_4248 <- getRegister v_2800;
      setRegister (lhs.of_reg v_2801) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4245 0 32) 24 8) (MInt2Float (extract v_4248 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4245 32 64) 24 8) (MInt2Float (extract v_4248 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4245 64 96) 24 8) (MInt2Float (extract v_4248 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4245 96 128) 24 8) (MInt2Float (extract v_4248 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2795 : Mem) (v_2796 : reg (bv 128)) => do
      v_8813 <- getRegister v_2796;
      v_8816 <- evaluateAddress v_2795;
      v_8817 <- load v_8816 16;
      setRegister (lhs.of_reg v_2796) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8813 0 32) 24 8) (MInt2Float (extract v_8817 0 32) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8813 32 64) 24 8) (MInt2Float (extract v_8817 32 64) 24 8)) 32) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8813 64 96) 24 8) (MInt2Float (extract v_8817 64 96) 24 8)) 32) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8813 96 128) 24 8) (MInt2Float (extract v_8817 96 128) 24 8)) 32))));
      pure ()
    pat_end
