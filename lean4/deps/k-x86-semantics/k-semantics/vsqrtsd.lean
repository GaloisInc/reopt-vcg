def vsqrtsd1 : instruction :=
  definst "vsqrtsd" $ do
    pattern fun (v_3058 : reg (bv 128)) (v_3059 : reg (bv 128)) (v_3060 : reg (bv 128)) => do
      v_7078 <- getRegister v_3059;
      v_7080 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3060) (concat (extract v_7078 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_7080 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 128)) (v_3054 : reg (bv 128)) => do
      v_13014 <- getRegister v_3053;
      v_13016 <- evaluateAddress v_3052;
      v_13017 <- load v_13016 8;
      setRegister (lhs.of_reg v_3054) (concat (extract v_13014 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_13017));
      pure ()
    pat_end
