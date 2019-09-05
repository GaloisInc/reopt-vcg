def vmovhps1 : instruction :=
  definst "vmovhps" $ do
    pattern fun (v_2888 : Mem) (v_2889 : reg (bv 128)) (v_2890 : reg (bv 128)) => do
      v_10181 <- evaluateAddress v_2888;
      v_10182 <- load v_10181 8;
      v_10183 <- getRegister v_2889;
      setRegister (lhs.of_reg v_2890) (concat v_10182 (extract v_10183 64 128));
      pure ()
    pat_end;
    pattern fun (v_2885 : reg (bv 128)) (v_2884 : Mem) => do
      v_12424 <- evaluateAddress v_2884;
      v_12425 <- getRegister v_2885;
      store v_12424 (extract v_12425 0 64) 8;
      pure ()
    pat_end
