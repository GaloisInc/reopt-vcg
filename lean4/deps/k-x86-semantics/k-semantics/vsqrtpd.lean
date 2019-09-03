def vsqrtpd1 : instruction :=
  definst "vsqrtpd" $ do
    pattern fun (v_2967 : reg (bv 128)) (v_2968 : reg (bv 128)) => do
      v_7054 <- getRegister v_2967;
      setRegister (lhs.of_reg v_2968) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7054 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7054 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2976 : reg (bv 256)) (v_2977 : reg (bv 256)) => do
      v_7065 <- getRegister v_2976;
      setRegister (lhs.of_reg v_2977) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7065 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7065 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7065 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7065 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2963 : Mem) (v_2964 : reg (bv 128)) => do
      v_13376 <- evaluateAddress v_2963;
      v_13377 <- load v_13376 16;
      setRegister (lhs.of_reg v_2964) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13377 0 64)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13377 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2972 : Mem) (v_2973 : reg (bv 256)) => do
      v_13384 <- evaluateAddress v_2972;
      v_13385 <- load v_13384 32;
      setRegister (lhs.of_reg v_2973) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13385 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13385 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13385 128 192)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_13385 192 256)))));
      pure ()
    pat_end
