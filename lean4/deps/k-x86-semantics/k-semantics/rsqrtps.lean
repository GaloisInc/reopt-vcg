def rsqrtps1 : instruction :=
  definst "rsqrtps" $ do
    pattern fun (v_2852 : reg (bv 128)) (v_2853 : reg (bv 128)) => do
      v_5812 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2853) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5812 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5812 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5812 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5812 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) (v_2849 : reg (bv 128)) => do
      v_12992 <- evaluateAddress v_2846;
      v_12993 <- load v_12992 16;
      setRegister (lhs.of_reg v_2849) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12993 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12993 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12993 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12993 96 128)) 24 8)) 32))));
      pure ()
    pat_end
