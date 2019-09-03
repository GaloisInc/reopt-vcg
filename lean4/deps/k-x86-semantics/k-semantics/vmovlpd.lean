def vmovlpd1 : instruction :=
  definst "vmovlpd" $ do
    pattern fun (v_2852 : Mem) (v_2853 : reg (bv 128)) (v_2854 : reg (bv 128)) => do
      v_11127 <- getRegister v_2853;
      v_11129 <- evaluateAddress v_2852;
      v_11130 <- load v_11129 8;
      setRegister (lhs.of_reg v_2854) (concat (extract v_11127 0 64) v_11130);
      pure ()
    pat_end;
    pattern fun (v_2849 : reg (bv 128)) (v_2848 : Mem) => do
      v_13625 <- evaluateAddress v_2848;
      v_13626 <- getRegister v_2849;
      store v_13625 (extract v_13626 64 128) 8;
      pure ()
    pat_end
