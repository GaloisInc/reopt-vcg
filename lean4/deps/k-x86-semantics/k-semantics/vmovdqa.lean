def vmovdqa1 : instruction :=
  definst "vmovdqa" $ do
    pattern fun (v_2843 : reg (bv 128)) (v_2842 : Mem) => do
      v_9328 <- evaluateAddress v_2842;
      v_9329 <- getRegister v_2843;
      store v_9328 v_9329 16;
      pure ()
    pat_end;
    pattern fun (v_2847 : reg (bv 256)) (v_2846 : Mem) => do
      v_9331 <- evaluateAddress v_2846;
      v_9332 <- getRegister v_2847;
      store v_9331 v_9332 32;
      pure ()
    pat_end;
    pattern fun (v_2850 : Mem) (v_2851 : reg (bv 128)) => do
      v_10186 <- evaluateAddress v_2850;
      v_10187 <- load v_10186 16;
      setRegister (lhs.of_reg v_2851) v_10187;
      pure ()
    pat_end;
    pattern fun (v_2859 : Mem) (v_2860 : reg (bv 256)) => do
      v_10189 <- evaluateAddress v_2859;
      v_10190 <- load v_10189 32;
      setRegister (lhs.of_reg v_2860) v_10190;
      pure ()
    pat_end
