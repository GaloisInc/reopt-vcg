def vmovhpd1 : instruction :=
  definst "vmovhpd" $ do
    pattern fun (v_2815 : Mem) (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_10308 <- evaluateAddress v_2815;
      v_10309 <- load v_10308 8;
      v_10310 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2817) (concat v_10309 (extract v_10310 64 128));
      pure ()
    pat_end;
    pattern fun (v_2812 : reg (bv 128)) (v_2811 : Mem) => do
      v_12740 <- evaluateAddress v_2811;
      v_12741 <- getRegister v_2812;
      store v_12740 (extract v_12741 0 64) 8;
      pure ()
    pat_end
