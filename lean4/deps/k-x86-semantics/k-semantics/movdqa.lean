def movdqa1 : instruction :=
  definst "movdqa" $ do
    pattern fun (v_2444 : reg (bv 128)) (v_2445 : reg (bv 128)) => do
      v_3871 <- getRegister v_2444;
      setRegister (lhs.of_reg v_2445) v_3871;
      pure ()
    pat_end;
    pattern fun (v_2437 : reg (bv 128)) (v_2436 : Mem) => do
      v_8559 <- evaluateAddress v_2436;
      v_8560 <- getRegister v_2437;
      store v_8559 v_8560 16;
      pure ()
    pat_end;
    pattern fun (v_2440 : Mem) (v_2441 : reg (bv 128)) => do
      v_8822 <- evaluateAddress v_2440;
      v_8823 <- load v_8822 16;
      setRegister (lhs.of_reg v_2441) v_8823;
      pure ()
    pat_end
