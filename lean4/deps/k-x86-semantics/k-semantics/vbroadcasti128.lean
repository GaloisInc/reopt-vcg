def vbroadcasti1281 : instruction :=
  definst "vbroadcasti128" $ do
    pattern fun (v_2881 : Mem) (v_2882 : reg (bv 256)) => do
      v_11426 <- evaluateAddress v_2881;
      v_11427 <- load v_11426 16;
      setRegister (lhs.of_reg v_2882) (concat v_11427 v_11427);
      pure ()
    pat_end
