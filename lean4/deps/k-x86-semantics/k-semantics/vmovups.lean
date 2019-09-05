def vmovups1 : instruction :=
  definst "vmovups" $ do
    pattern fun (v_3110 : Mem) (v_3111 : reg (bv 128)) => do
      v_10280 <- evaluateAddress v_3110;
      v_10281 <- load v_10280 16;
      setRegister (lhs.of_reg v_3111) v_10281;
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) (v_3120 : reg (bv 256)) => do
      v_10283 <- evaluateAddress v_3119;
      v_10284 <- load v_10283 32;
      setRegister (lhs.of_reg v_3120) v_10284;
      pure ()
    pat_end;
    pattern fun (v_3103 : reg (bv 128)) (v_3102 : Mem) => do
      v_12465 <- evaluateAddress v_3102;
      v_12466 <- getRegister v_3103;
      store v_12465 v_12466 16;
      pure ()
    pat_end;
    pattern fun (v_3107 : reg (bv 256)) (v_3106 : Mem) => do
      v_12468 <- evaluateAddress v_3106;
      v_12469 <- getRegister v_3107;
      store v_12468 v_12469 32;
      pure ()
    pat_end
