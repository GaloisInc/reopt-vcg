def vmovntps1 : instruction :=
  definst "vmovntps" $ do
    pattern fun (v_3007 : reg (bv 128)) (v_3006 : Mem) => do
      v_12472 <- evaluateAddress v_3006;
      v_12473 <- getRegister v_3007;
      store v_12472 v_12473 16;
      pure ()
    pat_end;
    pattern fun (v_3011 : reg (bv 256)) (v_3010 : Mem) => do
      v_12475 <- evaluateAddress v_3010;
      v_12476 <- getRegister v_3011;
      store v_12475 v_12476 32;
      pure ()
    pat_end
