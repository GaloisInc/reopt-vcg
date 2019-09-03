def movntps1 : instruction :=
  definst "movntps" $ do
    pattern fun (v_2554 : reg (bv 128)) (v_2553 : Mem) => do
      v_8627 <- evaluateAddress v_2553;
      v_8628 <- getRegister v_2554;
      store v_8627 v_8628 16;
      pure ()
    pat_end
