def vmovhpd1 : instruction :=
  definst "vmovhpd" $ do
    pattern fun (v_2879 : Mem) (v_2880 : reg (bv 128)) (v_2881 : reg (bv 128)) => do
      v_10174 <- evaluateAddress v_2879;
      v_10175 <- load v_10174 8;
      v_10176 <- getRegister v_2880;
      setRegister (lhs.of_reg v_2881) (concat v_10175 (extract v_10176 64 128));
      pure ()
    pat_end;
    pattern fun (v_2876 : reg (bv 128)) (v_2875 : Mem) => do
      v_12420 <- evaluateAddress v_2875;
      v_12421 <- getRegister v_2876;
      store v_12420 (extract v_12421 0 64) 8;
      pure ()
    pat_end
