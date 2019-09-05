def rsqrtss1 : instruction :=
  definst "rsqrtss" $ do
    pattern fun (v_2926 : reg (bv 128)) (v_2927 : reg (bv 128)) => do
      v_5583 <- getRegister v_2927;
      v_5585 <- getRegister v_2926;
      setRegister (lhs.of_reg v_2927) (concat (extract v_5583 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5585 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) (v_2922 : reg (bv 128)) => do
      v_11325 <- getRegister v_2922;
      v_11327 <- evaluateAddress v_2921;
      v_11328 <- load v_11327 4;
      setRegister (lhs.of_reg v_2922) (concat (extract v_11325 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_11328) 24 8)) 32));
      pure ()
    pat_end
