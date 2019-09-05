def vbroadcasti1281 : instruction :=
  definst "vbroadcasti128" $ do
    pattern fun (v_2934 : Mem) (v_2935 : reg (bv 256)) => do
      v_9652 <- evaluateAddress v_2934;
      v_9653 <- load v_9652 16;
      setRegister (lhs.of_reg v_2935) (concat v_9653 v_9653);
      pure ()
    pat_end
