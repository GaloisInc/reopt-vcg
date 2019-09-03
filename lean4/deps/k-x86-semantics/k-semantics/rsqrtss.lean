def rsqrtss1 : instruction :=
  definst "rsqrtss" $ do
    pattern fun (v_2861 : reg (bv 128)) (v_2862 : reg (bv 128)) => do
      v_5841 <- getRegister v_2862;
      v_5843 <- getRegister v_2861;
      setRegister (lhs.of_reg v_2862) (concat (extract v_5841 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_5843 96 128)) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2855 : Mem) (v_2858 : reg (bv 128)) => do
      v_13018 <- getRegister v_2858;
      v_13020 <- evaluateAddress v_2855;
      v_13021 <- load v_13020 4;
      setRegister (lhs.of_reg v_2858) (concat (extract v_13018 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_13021) 24 8)) 32));
      pure ()
    pat_end
