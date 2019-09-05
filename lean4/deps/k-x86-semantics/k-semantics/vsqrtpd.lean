def vsqrtpd1 : instruction :=
  definst "vsqrtpd" $ do
    pattern fun (v_3021 : reg (bv 128)) (v_3022 : reg (bv 128)) => do
      v_7003 <- getRegister v_3021;
      setRegister (lhs.of_reg v_3022) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7003 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7003 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3030 : reg (bv 256)) (v_3031 : reg (bv 256)) => do
      v_7014 <- getRegister v_3030;
      setRegister (lhs.of_reg v_3031) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7014 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7014 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7014 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7014 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3016 : Mem) (v_3017 : reg (bv 128)) => do
      v_12952 <- evaluateAddress v_3016;
      v_12953 <- load v_12952 16;
      setRegister (lhs.of_reg v_3017) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12953 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12953 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3025 : Mem) (v_3026 : reg (bv 256)) => do
      v_12960 <- evaluateAddress v_3025;
      v_12961 <- load v_12960 32;
      setRegister (lhs.of_reg v_3026) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12961 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12961 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12961 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12961 192 256)))));
      pure ()
    pat_end
