def vmovlpd1 : instruction :=
  definst "vmovlpd" $ do
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 128)) (v_2930 : reg (bv 128)) => do
      v_10215 <- getRegister v_2929;
      v_10217 <- evaluateAddress v_2928;
      v_10218 <- load v_10217 8;
      setRegister (lhs.of_reg v_2930) (concat (extract v_10215 0 64) v_10218);
      pure ()
    pat_end;
    pattern fun (v_2925 : reg (bv 128)) (v_2924 : Mem) => do
      v_12455 <- evaluateAddress v_2924;
      v_12456 <- getRegister v_2925;
      store v_12455 (extract v_12456 64 128) 8;
      pure ()
    pat_end
