def rsqrtps1 : instruction :=
  definst "rsqrtps" $ do
    pattern fun (v_2864 : reg (bv 128)) (v_2865 : reg (bv 128)) => do
      v_5830 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2865) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5830 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5830 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5830 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5830 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2859 : Mem) (v_2860 : reg (bv 128)) => do
      v_12916 <- evaluateAddress v_2859;
      v_12917 <- load v_12916 16;
      setRegister (lhs.of_reg v_2860) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12917 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12917 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12917 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12917 96 128)) 24 8)) 32))));
      pure ()
    pat_end
