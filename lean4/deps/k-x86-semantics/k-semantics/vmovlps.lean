def vmovlps1 : instruction :=
  definst "vmovlps" $ do
    pattern fun (v_2861 : Mem) (v_2862 : reg (bv 128)) (v_2863 : reg (bv 128)) => do
      v_11134 <- getRegister v_2862;
      v_11136 <- evaluateAddress v_2861;
      v_11137 <- load v_11136 8;
      setRegister (lhs.of_reg v_2863) (concat (extract v_11134 0 64) v_11137);
      pure ()
    pat_end;
    pattern fun (v_2858 : reg (bv 128)) (v_2857 : Mem) => do
      v_13629 <- evaluateAddress v_2857;
      v_13630 <- getRegister v_2858;
      store v_13629 (extract v_13630 64 128) 8;
      pure ()
    pat_end
