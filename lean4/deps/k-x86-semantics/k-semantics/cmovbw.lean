def cmovbw1 : instruction :=
  definst "cmovbw" $ do
    pattern fun (v_2587 : reg (bv 16)) (v_2588 : reg (bv 16)) => do
      v_4253 <- getRegister cf;
      v_4254 <- getRegister v_2587;
      v_4255 <- getRegister v_2588;
      setRegister (lhs.of_reg v_2588) (mux v_4253 v_4254 v_4255);
      pure ()
    pat_end;
    pattern fun (v_2583 : Mem) (v_2584 : reg (bv 16)) => do
      v_7730 <- getRegister cf;
      v_7731 <- evaluateAddress v_2583;
      v_7732 <- load v_7731 2;
      v_7733 <- getRegister v_2584;
      setRegister (lhs.of_reg v_2584) (mux v_7730 v_7732 v_7733);
      pure ()
    pat_end
