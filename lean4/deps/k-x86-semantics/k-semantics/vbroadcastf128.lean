def vbroadcastf1281 : instruction :=
  definst "vbroadcastf128" $ do
    pattern fun (v_2930 : Mem) (v_2931 : reg (bv 256)) => do
      v_9648 <- evaluateAddress v_2930;
      v_9649 <- load v_9648 16;
      setRegister (lhs.of_reg v_2931) (concat v_9649 v_9649);
      pure ()
    pat_end
