def sqrtpd1 : instruction :=
  definst "sqrtpd" $ do
    pattern fun (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) => do
      v_6728 <- getRegister v_3057;
      setRegister (lhs.of_reg v_3058) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6728 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6728 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 128)) => do
      v_10249 <- evaluateAddress v_3052;
      v_10250 <- load v_10249 16;
      setRegister (lhs.of_reg v_3053) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_10250 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_10250 64 128)));
      pure ()
    pat_end
