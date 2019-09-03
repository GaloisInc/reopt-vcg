def rcpps1 : instruction :=
  definst "rcpps" $ do
    pattern fun (v_2430 : reg (bv 128)) (v_2431 : reg (bv 128)) => do
      v_4190 <- getRegister v_2430;
      setRegister (lhs.of_reg v_2431) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4190 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4190 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4190 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4190 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2427 : reg (bv 128)) => do
      v_12815 <- evaluateAddress v_2424;
      v_12816 <- load v_12815 16;
      setRegister (lhs.of_reg v_2427) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12816 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12816 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12816 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12816 96 128) 24 8)) 32))));
      pure ()
    pat_end
