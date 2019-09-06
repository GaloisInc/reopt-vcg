def rcpps1 : instruction :=
  definst "rcpps" $ do
    pattern fun (v_2521 : reg (bv 128)) (v_2522 : reg (bv 128)) => do
      v_4211 <- getRegister v_2521;
      setRegister (lhs.of_reg v_2522) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4211 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4211 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4211 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_4211 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2515 : Mem) (v_2518 : reg (bv 128)) => do
      v_10406 <- evaluateAddress v_2515;
      v_10407 <- load v_10406 16;
      setRegister (lhs.of_reg v_2518) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_10407 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_10407 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_10407 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_10407 96 128) 24 8)) 32))));
      pure ()
    pat_end
