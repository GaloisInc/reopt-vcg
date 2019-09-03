def vbroadcastf1281 : instruction :=
  definst "vbroadcastf128" $ do
    pattern fun (v_2864 : Mem) (v_2865 : reg (bv 256)) => do
      v_9880 <- evaluateAddress v_2864;
      v_9881 <- load v_9880 16;
      setRegister (lhs.of_reg v_2865) (concat v_9881 v_9881);
      pure ()
    pat_end
