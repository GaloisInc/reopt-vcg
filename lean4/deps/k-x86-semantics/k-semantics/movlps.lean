def movlps1 : instruction :=
  definst "movlps" $ do
    pattern fun (v_2569 : reg (bv 128)) (v_2568 : Mem) => do
      v_8453 <- evaluateAddress v_2568;
      v_8454 <- getRegister v_2569;
      store v_8453 (extract v_8454 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2572 : Mem) (v_2573 : reg (bv 128)) => do
      v_8713 <- getRegister v_2573;
      v_8715 <- evaluateAddress v_2572;
      v_8716 <- load v_8715 8;
      setRegister (lhs.of_reg v_2573) (concat (extract v_8713 0 64) v_8716);
      pure ()
    pat_end
