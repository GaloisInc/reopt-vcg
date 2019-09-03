def sqrtsd1 : instruction :=
  definst "sqrtsd" $ do
    pattern fun (v_3088 : reg (bv 128)) (v_3089 : reg (bv 128)) => do
      v_6752 <- getRegister v_3089;
      v_6754 <- getRegister v_3088;
      setRegister (lhs.of_reg v_3089) (concat (extract v_6752 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6754 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3083 : Mem) (v_3084 : reg (bv 128)) => do
      v_10293 <- getRegister v_3084;
      v_10295 <- evaluateAddress v_3083;
      v_10296 <- load v_10295 8;
      setRegister (lhs.of_reg v_3084) (concat (extract v_10293 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_10296));
      pure ()
    pat_end
