def movdqu1 : instruction :=
  definst "movdqu" $ do
    pattern fun (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_3959 <- getRegister v_2533;
      setRegister (lhs.of_reg v_2534) v_3959;
      pure ()
    pat_end;
    pattern fun (v_2526 : reg (bv 128)) (v_2525 : Mem) => do
      v_8454 <- evaluateAddress v_2525;
      v_8455 <- getRegister v_2526;
      store v_8454 v_8455 16;
      pure ()
    pat_end;
    pattern fun (v_2529 : Mem) (v_2530 : reg (bv 128)) => do
      v_8716 <- evaluateAddress v_2529;
      v_8717 <- load v_8716 16;
      setRegister (lhs.of_reg v_2530) v_8717;
      pure ()
    pat_end
