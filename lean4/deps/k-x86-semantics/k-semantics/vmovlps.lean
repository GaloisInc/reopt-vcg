def vmovlps1 : instruction :=
  definst "vmovlps" $ do
    pattern fun (v_2937 : Mem) (v_2938 : reg (bv 128)) (v_2939 : reg (bv 128)) => do
      v_10222 <- getRegister v_2938;
      v_10224 <- evaluateAddress v_2937;
      v_10225 <- load v_10224 8;
      setRegister (lhs.of_reg v_2939) (concat (extract v_10222 0 64) v_10225);
      pure ()
    pat_end;
    pattern fun (v_2934 : reg (bv 128)) (v_2933 : Mem) => do
      v_12459 <- evaluateAddress v_2933;
      v_12460 <- getRegister v_2934;
      store v_12459 (extract v_12460 64 128) 8;
      pure ()
    pat_end
