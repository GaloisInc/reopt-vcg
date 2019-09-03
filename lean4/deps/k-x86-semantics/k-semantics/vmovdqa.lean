def vmovdqa1 : instruction :=
  definst "vmovdqa" $ do
    pattern fun (v_2767 : reg (bv 128)) (v_2766 : Mem) => do
      v_9856 <- evaluateAddress v_2766;
      v_9857 <- getRegister v_2767;
      store v_9856 v_9857 16;
      pure ()
    pat_end;
    pattern fun (v_2771 : reg (bv 256)) (v_2770 : Mem) => do
      v_9859 <- evaluateAddress v_2770;
      v_9860 <- getRegister v_2771;
      store v_9859 v_9860 32;
      pure ()
    pat_end;
    pattern fun (v_2774 : Mem) (v_2775 : reg (bv 128)) => do
      v_11098 <- evaluateAddress v_2774;
      v_11099 <- load v_11098 16;
      setRegister (lhs.of_reg v_2775) v_11099;
      pure ()
    pat_end;
    pattern fun (v_2783 : Mem) (v_2784 : reg (bv 256)) => do
      v_11101 <- evaluateAddress v_2783;
      v_11102 <- load v_11101 32;
      setRegister (lhs.of_reg v_2784) v_11102;
      pure ()
    pat_end
