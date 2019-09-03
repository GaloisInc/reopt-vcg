def vmovntps1 : instruction :=
  definst "vmovntps" $ do
    pattern fun (v_2918 : reg (bv 128)) (v_2917 : Mem) => do
      v_12765 <- evaluateAddress v_2917;
      v_12766 <- getRegister v_2918;
      store v_12765 v_12766 16;
      pure ()
    pat_end;
    pattern fun (v_2922 : reg (bv 256)) (v_2921 : Mem) => do
      v_12768 <- evaluateAddress v_2921;
      v_12769 <- getRegister v_2922;
      store v_12768 v_12769 32;
      pure ()
    pat_end
