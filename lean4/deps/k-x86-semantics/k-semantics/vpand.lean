def vpand1 : instruction :=
  definst "vpand" $ do
    pattern fun (v_2516 : Mem) (v_2517 : reg (bv 128)) (v_2518 : reg (bv 128)) => do
      v_15195 <- getRegister v_2517;
      v_15196 <- evaluateAddress v_2516;
      v_15197 <- load v_15196 16;
      setRegister (lhs.of_reg v_2518) (bv_and v_15195 v_15197);
      pure ()
    pat_end;
    pattern fun (v_2527 : Mem) (v_2528 : reg (bv 256)) (v_2529 : reg (bv 256)) => do
      v_15200 <- getRegister v_2528;
      v_15201 <- evaluateAddress v_2527;
      v_15202 <- load v_15201 32;
      setRegister (lhs.of_reg v_2529) (bv_and v_15200 v_15202);
      pure ()
    pat_end
