def vrsqrtps1 : instruction :=
  definst "vrsqrtps" $ do
    pattern fun (v_2940 : reg (bv 128)) (v_2941 : reg (bv 128)) => do
      v_6752 <- getRegister v_2940;
      setRegister (lhs.of_reg v_2941) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6752 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6752 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6752 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6752 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2949 : reg (bv 256)) (v_2950 : reg (bv 256)) => do
      v_6781 <- getRegister v_2949;
      setRegister (lhs.of_reg v_2950) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 64 96)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 96 128)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 128 160)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 160 192)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 192 224)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6781 224 256)) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2935 : Mem) (v_2936 : reg (bv 128)) => do
      v_12732 <- evaluateAddress v_2935;
      v_12733 <- load v_12732 16;
      setRegister (lhs.of_reg v_2936) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12733 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12733 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12733 64 96)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12733 96 128)) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2944 : Mem) (v_2945 : reg (bv 256)) => do
      v_12758 <- evaluateAddress v_2944;
      v_12759 <- load v_12758 32;
      setRegister (lhs.of_reg v_2945) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 0 32)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 32 64)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 64 96)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 96 128)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 128 160)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 160 192)) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 192 224)) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_12759 224 256)) 24 8)) 32))))))));
      pure ()
    pat_end
