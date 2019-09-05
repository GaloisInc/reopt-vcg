def rcpps1 : instruction :=
  definst "rcpps" $ do
    pattern fun (v_2495 : reg (bv 128)) (v_2496 : reg (bv 128)) => do
      v_4218 <- getRegister v_2495;
      setRegister (lhs.of_reg v_2496) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4218 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4218 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4218 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4218 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2490 : Mem) (v_2491 : reg (bv 128)) => do
      v_11150 <- evaluateAddress v_2490;
      v_11151 <- load v_11150 16;
      setRegister (lhs.of_reg v_2491) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_11151 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_11151 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_11151 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_11151 96 128) 24 8)) 32))));
      pure ()
    pat_end
