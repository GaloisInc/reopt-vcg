def vandps1 : instruction :=
  definst "vandps" $ do
    pattern fun (v_2738 : Mem) (v_2741 : reg (bv 128)) (v_2742 : reg (bv 128)) => do
      v_9622 <- getRegister v_2741;
      v_9623 <- evaluateAddress v_2738;
      v_9624 <- load v_9623 16;
      setRegister (lhs.of_reg v_2742) (bv_and v_9622 v_9624);
      pure ()
    pat_end;
    pattern fun (v_2749 : Mem) (v_2750 : reg (bv 256)) (v_2751 : reg (bv 256)) => do
      v_9627 <- getRegister v_2750;
      v_9628 <- evaluateAddress v_2749;
      v_9629 <- load v_9628 32;
      setRegister (lhs.of_reg v_2751) (bv_and v_9627 v_9629);
      pure ()
    pat_end
