def movnti1 : instruction :=
  definst "movnti" $ do
    pattern fun (v_2605 : reg (bv 32)) (v_2604 : Mem) => do
      v_8462 <- evaluateAddress v_2604;
      v_8463 <- getRegister v_2605;
      store v_8462 v_8463 4;
      pure ()
    pat_end;
    pattern fun (v_2609 : reg (bv 64)) (v_2608 : Mem) => do
      v_8465 <- evaluateAddress v_2608;
      v_8466 <- getRegister v_2609;
      store v_8465 v_8466 8;
      pure ()
    pat_end
