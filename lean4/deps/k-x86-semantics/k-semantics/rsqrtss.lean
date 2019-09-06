def rsqrtss1 : instruction :=
  definst "rsqrtss" $ do
    pattern fun (v_2952 : reg (bv 128)) (v_2953 : reg (bv 128)) => do
      v_5291 <- getRegister v_2953;
      v_5293 <- getRegister v_2952;
      setRegister (lhs.of_reg v_2953) (concat (extract v_5291 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5293 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2946 : Mem) (v_2949 : reg (bv 128)) => do
      v_10581 <- getRegister v_2949;
      v_10583 <- evaluateAddress v_2946;
      v_10584 <- load v_10583 4;
      setRegister (lhs.of_reg v_2949) (concat (extract v_10581 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_10584) 24 8)) 32));
      pure ()
    pat_end
