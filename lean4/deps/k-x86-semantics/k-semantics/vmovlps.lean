def vmovlps1 : instruction :=
  definst "vmovlps" $ do
    pattern fun (v_2912 : Mem) (v_2913 : reg (bv 128)) (v_2914 : reg (bv 128)) => do
      v_10195 <- getRegister v_2913;
      v_10197 <- evaluateAddress v_2912;
      v_10198 <- load v_10197 8;
      setRegister (lhs.of_reg v_2914) (concat (extract v_10195 0 64) v_10198);
      pure ()
    pat_end;
    pattern fun (v_2909 : reg (bv 128)) (v_2908 : Mem) => do
      v_12432 <- evaluateAddress v_2908;
      v_12433 <- getRegister v_2909;
      store v_12432 (extract v_12433 64 128) 8;
      pure ()
    pat_end
