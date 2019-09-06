def movlps1 : instruction :=
  definst "movlps" $ do
    pattern fun (v_2595 : reg (bv 128)) (v_2594 : Mem) => do
      v_8480 <- evaluateAddress v_2594;
      v_8481 <- getRegister v_2595;
      store v_8480 (extract v_8481 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2598 : Mem) (v_2599 : reg (bv 128)) => do
      v_8740 <- getRegister v_2599;
      v_8742 <- evaluateAddress v_2598;
      v_8743 <- load v_8742 8;
      setRegister (lhs.of_reg v_2599) (concat (extract v_8740 0 64) v_8743);
      pure ()
    pat_end
