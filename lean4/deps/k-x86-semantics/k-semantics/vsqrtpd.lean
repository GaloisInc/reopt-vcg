def vsqrtpd1 : instruction :=
  definst "vsqrtpd" $ do
    pattern fun (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_7030 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3049) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7030 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7030 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3057 : reg (bv 256)) (v_3058 : reg (bv 256)) => do
      v_7041 <- getRegister v_3057;
      setRegister (lhs.of_reg v_3058) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7041 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7041 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7041 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7041 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3043 : Mem) (v_3044 : reg (bv 128)) => do
      v_12979 <- evaluateAddress v_3043;
      v_12980 <- load v_12979 16;
      setRegister (lhs.of_reg v_3044) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12980 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12980 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 256)) => do
      v_12987 <- evaluateAddress v_3052;
      v_12988 <- load v_12987 32;
      setRegister (lhs.of_reg v_3053) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12988 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12988 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12988 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_12988 192 256)))));
      pure ()
    pat_end
