def vrsqrtss1 : instruction :=
  definst "vrsqrtss" $ do
    pattern fun (v_2959 : reg (bv 128)) (v_2960 : reg (bv 128)) (v_2961 : reg (bv 128)) => do
      v_6835 <- getRegister v_2960;
      v_6837 <- getRegister v_2959;
      setRegister (lhs.of_reg v_2961) (concat (extract v_6835 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6837 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2953 : Mem) (v_2954 : reg (bv 128)) (v_2955 : reg (bv 128)) => do
      v_12808 <- getRegister v_2954;
      v_12810 <- evaluateAddress v_2953;
      v_12811 <- load v_12810 4;
      setRegister (lhs.of_reg v_2955) (concat (extract v_12808 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_12811) 24 8)) 32));
      pure ()
    pat_end
