def vrsqrtss1 : instruction :=
  definst "vrsqrtss" $ do
    pattern fun (v_2905 : reg (bv 128)) (v_2906 : reg (bv 128)) (v_2907 : reg (bv 128)) => do
      v_6864 <- getRegister v_2906;
      v_6866 <- getRegister v_2905;
      setRegister (lhs.of_reg v_2907) (concat (extract v_6864 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6866 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2900 : Mem) (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) => do
      v_13210 <- getRegister v_2901;
      v_13212 <- evaluateAddress v_2900;
      v_13213 <- load v_13212 4;
      setRegister (lhs.of_reg v_2902) (concat (extract v_13210 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_13213) 24 8)) 32));
      pure ()
    pat_end
