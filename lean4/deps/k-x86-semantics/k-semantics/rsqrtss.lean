def rsqrtss1 : instruction :=
  definst "rsqrtss" $ do
    pattern fun (v_2873 : reg (bv 128)) (v_2874 : reg (bv 128)) => do
      v_5859 <- getRegister v_2874;
      v_5861 <- getRegister v_2873;
      setRegister (lhs.of_reg v_2874) (concat (extract v_5859 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5861 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2868 : Mem) (v_2869 : reg (bv 128)) => do
      v_12942 <- getRegister v_2869;
      v_12944 <- evaluateAddress v_2868;
      v_12945 <- load v_12944 4;
      setRegister (lhs.of_reg v_2869) (concat (extract v_12942 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_12945) 24 8)) 32));
      pure ()
    pat_end
