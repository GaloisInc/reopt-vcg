def vmovups1 : instruction :=
  definst "vmovups" $ do
    pattern fun (v_3135 : Mem) (v_3136 : reg (bv 128)) => do
      v_10307 <- evaluateAddress v_3135;
      v_10308 <- load v_10307 16;
      setRegister (lhs.of_reg v_3136) v_10308;
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3145 : reg (bv 256)) => do
      v_10310 <- evaluateAddress v_3144;
      v_10311 <- load v_10310 32;
      setRegister (lhs.of_reg v_3145) v_10311;
      pure ()
    pat_end;
    pattern fun (v_3128 : reg (bv 128)) (v_3127 : Mem) => do
      v_12492 <- evaluateAddress v_3127;
      v_12493 <- getRegister v_3128;
      store v_12492 v_12493 16;
      pure ()
    pat_end;
    pattern fun (v_3132 : reg (bv 256)) (v_3131 : Mem) => do
      v_12495 <- evaluateAddress v_3131;
      v_12496 <- getRegister v_3132;
      store v_12495 v_12496 32;
      pure ()
    pat_end
