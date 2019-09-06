def vbroadcasti1281 : instruction :=
  definst "vbroadcasti128" $ do
    pattern fun (v_2959 : Mem) (v_2960 : reg (bv 256)) => do
      v_9679 <- evaluateAddress v_2959;
      v_9680 <- load v_9679 16;
      setRegister (lhs.of_reg v_2960) (concat v_9680 v_9680);
      pure ()
    pat_end
