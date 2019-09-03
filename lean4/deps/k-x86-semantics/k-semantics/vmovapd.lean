def vmovapd1 : instruction :=
  definst "vmovapd" $ do
    pattern fun (v_2686 : Mem) (v_2687 : reg (bv 128)) => do
      v_11065 <- evaluateAddress v_2686;
      v_11066 <- load v_11065 16;
      setRegister (lhs.of_reg v_2687) v_11066;
      pure ()
    pat_end;
    pattern fun (v_2695 : Mem) (v_2696 : reg (bv 256)) => do
      v_11068 <- evaluateAddress v_2695;
      v_11069 <- load v_11068 32;
      setRegister (lhs.of_reg v_2696) v_11069;
      pure ()
    pat_end;
    pattern fun (v_2679 : reg (bv 128)) (v_2678 : Mem) => do
      v_13599 <- evaluateAddress v_2678;
      v_13600 <- getRegister v_2679;
      store v_13599 v_13600 16;
      pure ()
    pat_end;
    pattern fun (v_2683 : reg (bv 256)) (v_2682 : Mem) => do
      v_13602 <- evaluateAddress v_2682;
      v_13603 <- getRegister v_2683;
      store v_13602 v_13603 32;
      pure ()
    pat_end
