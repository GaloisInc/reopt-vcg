def sqrtpd1 : instruction :=
  definst "sqrtpd" $ do
    pattern fun (v_3148 : reg (bv 128)) (v_3149 : reg (bv 128)) => do
      v_5474 <- getRegister v_3148;
      setRegister (lhs.of_reg v_3149) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_5474 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_5474 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3145 : reg (bv 128)) => do
      v_8537 <- evaluateAddress v_3144;
      v_8538 <- load v_8537 16;
      setRegister (lhs.of_reg v_3145) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_8538 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_8538 64 128)));
      pure ()
    pat_end
