def vrsqrtss1 : instruction :=
  definst "vrsqrtss" $ do
    pattern fun (v_2986 : reg (bv 128)) (v_2987 : reg (bv 128)) (v_2988 : reg (bv 128)) => do
      v_6862 <- getRegister v_2987;
      v_6864 <- getRegister v_2986;
      setRegister (lhs.of_reg v_2988) (concat (extract v_6862 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6864 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2980 : Mem) (v_2981 : reg (bv 128)) (v_2982 : reg (bv 128)) => do
      v_12835 <- getRegister v_2981;
      v_12837 <- evaluateAddress v_2980;
      v_12838 <- load v_12837 4;
      setRegister (lhs.of_reg v_2982) (concat (extract v_12835 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_12838) 24 8)) 32));
      pure ()
    pat_end
