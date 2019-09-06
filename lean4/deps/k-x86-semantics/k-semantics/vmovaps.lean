def vmovaps1 : instruction :=
  definst "vmovaps" $ do
    pattern fun (v_2788 : Mem) (v_2789 : reg (bv 128)) => do
      v_10161 <- evaluateAddress v_2788;
      v_10162 <- load v_10161 16;
      setRegister (lhs.of_reg v_2789) v_10162;
      pure ()
    pat_end;
    pattern fun (v_2797 : Mem) (v_2798 : reg (bv 256)) => do
      v_10164 <- evaluateAddress v_2797;
      v_10165 <- load v_10164 32;
      setRegister (lhs.of_reg v_2798) v_10165;
      pure ()
    pat_end;
    pattern fun (v_2781 : reg (bv 128)) (v_2780 : Mem) => do
      v_12435 <- evaluateAddress v_2780;
      v_12436 <- getRegister v_2781;
      store v_12435 v_12436 16;
      pure ()
    pat_end;
    pattern fun (v_2785 : reg (bv 256)) (v_2784 : Mem) => do
      v_12438 <- evaluateAddress v_2784;
      v_12439 <- getRegister v_2785;
      store v_12438 v_12439 32;
      pure ()
    pat_end
