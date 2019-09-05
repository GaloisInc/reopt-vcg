def rsqrtps1 : instruction :=
  definst "rsqrtps" $ do
    pattern fun (v_2917 : reg (bv 128)) (v_2918 : reg (bv 128)) => do
      v_5554 <- getRegister v_2917;
      setRegister (lhs.of_reg v_2918) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5554 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5554 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5554 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5554 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2912 : Mem) (v_2913 : reg (bv 128)) => do
      v_11299 <- evaluateAddress v_2912;
      v_11300 <- load v_11299 16;
      setRegister (lhs.of_reg v_2913) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_11300 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_11300 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_11300 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_11300 96 128)) 24 8)) 32))));
      pure ()
    pat_end
