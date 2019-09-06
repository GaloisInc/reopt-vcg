def vorpd1 : instruction :=
  definst "vorpd" $ do
    pattern fun (v_3219 : Mem) (v_3220 : reg (bv 128)) (v_3221 : reg (bv 128)) => do
      v_10473 <- getRegister v_3220;
      v_10474 <- evaluateAddress v_3219;
      v_10475 <- load v_10474 16;
      setRegister (lhs.of_reg v_3221) (bv_or v_10473 v_10475);
      pure ()
    pat_end;
    pattern fun (v_3230 : Mem) (v_3231 : reg (bv 256)) (v_3232 : reg (bv 256)) => do
      v_10478 <- getRegister v_3231;
      v_10479 <- evaluateAddress v_3230;
      v_10480 <- load v_10479 32;
      setRegister (lhs.of_reg v_3232) (bv_or v_10478 v_10480);
      pure ()
    pat_end
