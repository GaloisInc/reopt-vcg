def vsqrtsd1 : instruction :=
  definst "vsqrtsd" $ do
    pattern fun (v_3085 : reg (bv 128)) (v_3086 : reg (bv 128)) (v_3087 : reg (bv 128)) => do
      v_7105 <- getRegister v_3086;
      v_7107 <- getRegister v_3085;
      setRegister (lhs.of_reg v_3087) (concat (extract v_7105 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7107 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) (v_3080 : reg (bv 128)) (v_3081 : reg (bv 128)) => do
      v_13041 <- getRegister v_3080;
      v_13043 <- evaluateAddress v_3079;
      v_13044 <- load v_13043 8;
      setRegister (lhs.of_reg v_3081) (concat (extract v_13041 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_13044));
      pure ()
    pat_end
