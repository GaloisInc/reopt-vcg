def movnti1 : instruction :=
  definst "movnti" $ do
    pattern fun (v_2542 : reg (bv 32)) (v_2541 : Mem) => do
      v_8618 <- evaluateAddress v_2541;
      v_8619 <- getRegister v_2542;
      store v_8618 v_8619 4;
      pure ()
    pat_end;
    pattern fun (v_2546 : reg (bv 64)) (v_2545 : Mem) => do
      v_8621 <- evaluateAddress v_2545;
      v_8622 <- getRegister v_2546;
      store v_8621 v_8622 8;
      pure ()
    pat_end
