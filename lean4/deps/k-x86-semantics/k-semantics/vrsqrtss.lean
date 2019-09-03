def vrsqrtss1 : instruction :=
  definst "vrsqrtss" $ do
    pattern fun (v_2895 : reg (bv 128)) (v_2896 : reg (bv 128)) (v_2897 : reg (bv 128)) => do
      v_6921 <- getRegister v_2896;
      v_6923 <- getRegister v_2895;
      setRegister (lhs.of_reg v_2897) (concat (extract v_6921 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6923 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) (v_2890 : reg (bv 128)) (v_2891 : reg (bv 128)) => do
      v_13135 <- getRegister v_2890;
      v_13137 <- evaluateAddress v_2889;
      v_13138 <- load v_13137 4;
      setRegister (lhs.of_reg v_2891) (concat (extract v_13135 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_13138) 24 8)) 32));
      pure ()
    pat_end
