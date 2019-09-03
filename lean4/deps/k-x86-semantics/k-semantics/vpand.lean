def vpand1 : instruction :=
  definst "vpand" $ do
    pattern fun (v_2531 : Mem) (v_2527 : reg (bv 128)) (v_2528 : reg (bv 128)) => do
      v_14690 <- getRegister v_2527;
      v_14691 <- evaluateAddress v_2531;
      v_14692 <- load v_14691 16;
      setRegister (lhs.of_reg v_2528) (bv_and v_14690 v_14692);
      pure ()
    pat_end;
    pattern fun (v_2540 : Mem) (v_2541 : reg (bv 256)) (v_2542 : reg (bv 256)) => do
      v_14695 <- getRegister v_2541;
      v_14696 <- evaluateAddress v_2540;
      v_14697 <- load v_14696 32;
      setRegister (lhs.of_reg v_2542) (bv_and v_14695 v_14697);
      pure ()
    pat_end
