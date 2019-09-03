def movntps1 : instruction :=
  definst "movntps" $ do
    pattern fun (v_2567 : reg (bv 128)) (v_2566 : Mem) => do
      v_8607 <- evaluateAddress v_2566;
      v_8608 <- getRegister v_2567;
      store v_8607 v_8608 16;
      pure ()
    pat_end
