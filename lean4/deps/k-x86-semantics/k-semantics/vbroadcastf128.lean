def vbroadcastf1281 : instruction :=
  definst "vbroadcastf128" $ do
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 256)) => do
      v_9675 <- evaluateAddress v_2955;
      v_9676 <- load v_9675 16;
      setRegister (lhs.of_reg v_2956) (concat v_9676 v_9676);
      pure ()
    pat_end
