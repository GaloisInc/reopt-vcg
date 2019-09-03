def vsqrtpd1 : instruction :=
  definst "vsqrtpd" $ do
    pattern fun (v_2957 : reg (bv 128)) (v_2958 : reg (bv 128)) => do
      v_7111 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2958) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7111 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7111 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2965 : reg (bv 256)) (v_2966 : reg (bv 256)) => do
      v_7122 <- getRegister v_2965;
      setRegister (lhs.of_reg v_2966) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7122 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7122 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7122 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7122 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2952 : Mem) (v_2953 : reg (bv 128)) => do
      v_13301 <- evaluateAddress v_2952;
      v_13302 <- load v_13301 16;
      setRegister (lhs.of_reg v_2953) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13302 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13302 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2961 : Mem) (v_2962 : reg (bv 256)) => do
      v_13309 <- evaluateAddress v_2961;
      v_13310 <- load v_13309 32;
      setRegister (lhs.of_reg v_2962) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13310 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13310 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13310 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13310 192 256)))));
      pure ()
    pat_end
