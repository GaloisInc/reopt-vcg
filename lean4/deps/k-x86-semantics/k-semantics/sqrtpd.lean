def sqrtpd1 : instruction :=
  definst "sqrtpd" $ do
    pattern fun (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_6019 <- getRegister v_3120;
      setRegister (lhs.of_reg v_3121) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6019 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6019 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3117 : Mem) (v_3116 : reg (bv 128)) => do
      v_9144 <- evaluateAddress v_3117;
      v_9145 <- load v_9144 16;
      setRegister (lhs.of_reg v_3116) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_9145 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_9145 64 128)));
      pure ()
    pat_end
