def movdqu1 : instruction :=
  definst "movdqu" $ do
    pattern fun (v_2445 : reg (bv 128)) (v_2446 : reg (bv 128)) => do
      v_3868 <- getRegister v_2445;
      setRegister (lhs.of_reg v_2446) v_3868;
      pure ()
    pat_end;
    pattern fun (v_2437 : reg (bv 128)) (v_2436 : Mem) => do
      v_8583 <- evaluateAddress v_2436;
      v_8584 <- getRegister v_2437;
      store v_8583 v_8584 16;
      pure ()
    pat_end;
    pattern fun (v_2440 : Mem) (v_2441 : reg (bv 128)) => do
      v_8846 <- evaluateAddress v_2440;
      v_8847 <- load v_8846 16;
      setRegister (lhs.of_reg v_2441) v_8847;
      pure ()
    pat_end
