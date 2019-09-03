def vbroadcasti1281 : instruction :=
  definst "vbroadcasti128" $ do
    pattern fun (v_2868 : Mem) (v_2869 : reg (bv 256)) => do
      v_9884 <- evaluateAddress v_2868;
      v_9885 <- load v_9884 16;
      setRegister (lhs.of_reg v_2869) (concat v_9885 v_9885);
      pure ()
    pat_end
