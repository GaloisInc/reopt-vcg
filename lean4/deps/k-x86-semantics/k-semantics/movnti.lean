def movnti1 : instruction :=
  definst "movnti" $ do
    pattern fun (v_2631 : reg (bv 32)) (v_2630 : Mem) => do
      v_8489 <- evaluateAddress v_2630;
      v_8490 <- getRegister v_2631;
      store v_8489 v_8490 4;
      pure ()
    pat_end;
    pattern fun (v_2635 : reg (bv 64)) (v_2634 : Mem) => do
      v_8492 <- evaluateAddress v_2634;
      v_8493 <- getRegister v_2635;
      store v_8492 v_8493 8;
      pure ()
    pat_end
