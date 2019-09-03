def sqrtpd1 : instruction :=
  definst "sqrtpd" $ do
    pattern fun (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) => do
      v_6724 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3071) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6724 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6724 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3065 : Mem) (v_3066 : reg (bv 128)) => do
      v_10271 <- evaluateAddress v_3065;
      v_10272 <- load v_10271 16;
      setRegister (lhs.of_reg v_3066) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_10272 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_10272 64 128)));
      pure ()
    pat_end
