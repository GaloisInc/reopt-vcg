def rsqrtps1 : instruction :=
  definst "rsqrtps" $ do
    pattern fun (v_2943 : reg (bv 128)) (v_2944 : reg (bv 128)) => do
      v_5262 <- getRegister v_2943;
      setRegister (lhs.of_reg v_2944) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5262 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5262 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5262 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5262 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) (v_2940 : reg (bv 128)) => do
      v_10555 <- evaluateAddress v_2937;
      v_10556 <- load v_10555 16;
      setRegister (lhs.of_reg v_2940) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10556 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10556 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10556 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_10556 96 128)) 24 8)) 32))));
      pure ()
    pat_end
