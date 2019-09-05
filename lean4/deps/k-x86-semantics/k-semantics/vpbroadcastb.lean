def vpbroadcastb1 : instruction :=
  definst "vpbroadcastb" $ do
    pattern fun (v_2751 : reg (bv 128)) (v_2752 : reg (bv 128)) => do
      v_6888 <- getRegister v_2751;
      v_6889 <- eval (extract v_6888 120 128);
      setRegister (lhs.of_reg v_2752) (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 (concat v_6889 v_6889)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2761 : reg (bv 128)) (v_2759 : reg (bv 256)) => do
      v_6910 <- getRegister v_2761;
      v_6911 <- eval (extract v_6910 120 128);
      setRegister (lhs.of_reg v_2759) (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 (concat v_6911 v_6911)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) (v_2747 : reg (bv 128)) => do
      v_15537 <- evaluateAddress v_2746;
      v_15538 <- load v_15537 1;
      setRegister (lhs.of_reg v_2747) (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 (concat v_15538 v_15538)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2755 : Mem) (v_2756 : reg (bv 256)) => do
      v_15555 <- evaluateAddress v_2755;
      v_15556 <- load v_15555 1;
      setRegister (lhs.of_reg v_2756) (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 (concat v_15556 v_15556)))))))))))))))))))))))))))))));
      pure ()
    pat_end
