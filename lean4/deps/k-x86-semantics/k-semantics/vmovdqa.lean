def vmovdqa1 : instruction :=
  definst "vmovdqa" $ do
    pattern fun (v_2818 : reg (bv 128)) (v_2817 : Mem) => do
      v_9301 <- evaluateAddress v_2817;
      v_9302 <- getRegister v_2818;
      store v_9301 v_9302 16;
      pure ()
    pat_end;
    pattern fun (v_2822 : reg (bv 256)) (v_2821 : Mem) => do
      v_9304 <- evaluateAddress v_2821;
      v_9305 <- getRegister v_2822;
      store v_9304 v_9305 32;
      pure ()
    pat_end;
    pattern fun (v_2825 : Mem) (v_2826 : reg (bv 128)) => do
      v_10159 <- evaluateAddress v_2825;
      v_10160 <- load v_10159 16;
      setRegister (lhs.of_reg v_2826) v_10160;
      pure ()
    pat_end;
    pattern fun (v_2834 : Mem) (v_2835 : reg (bv 256)) => do
      v_10162 <- evaluateAddress v_2834;
      v_10163 <- load v_10162 32;
      setRegister (lhs.of_reg v_2835) v_10163;
      pure ()
    pat_end
