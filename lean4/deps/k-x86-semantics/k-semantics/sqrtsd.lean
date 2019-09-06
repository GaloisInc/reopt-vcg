def sqrtsd1 : instruction :=
  definst "sqrtsd" $ do
    pattern fun (v_3166 : reg (bv 128)) (v_3167 : reg (bv 128)) => do
      v_5502 <- getRegister v_3167;
      v_5504 <- getRegister v_3166;
      setRegister (lhs.of_reg v_3167) (concat (extract v_5502 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_5504 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3162 : Mem) (v_3163 : reg (bv 128)) => do
      v_8559 <- getRegister v_3163;
      v_8561 <- evaluateAddress v_3162;
      v_8562 <- load v_8561 8;
      setRegister (lhs.of_reg v_3163) (concat (extract v_8559 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_8562));
      pure ()
    pat_end
