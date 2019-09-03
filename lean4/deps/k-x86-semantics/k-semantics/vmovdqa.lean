def vmovdqa1 : instruction :=
  definst "vmovdqa" $ do
    pattern fun (v_2754 : reg (bv 128)) (v_2753 : Mem) => do
      v_9411 <- evaluateAddress v_2753;
      v_9412 <- getRegister v_2754;
      store v_9411 v_9412 16;
      pure ()
    pat_end;
    pattern fun (v_2758 : reg (bv 256)) (v_2757 : Mem) => do
      v_9414 <- evaluateAddress v_2757;
      v_9415 <- getRegister v_2758;
      store v_9414 v_9415 32;
      pure ()
    pat_end;
    pattern fun (v_2761 : Mem) (v_2762 : reg (bv 128)) => do
      v_10293 <- evaluateAddress v_2761;
      v_10294 <- load v_10293 16;
      setRegister (lhs.of_reg v_2762) v_10294;
      pure ()
    pat_end;
    pattern fun (v_2770 : Mem) (v_2771 : reg (bv 256)) => do
      v_10296 <- evaluateAddress v_2770;
      v_10297 <- load v_10296 32;
      setRegister (lhs.of_reg v_2771) v_10297;
      pure ()
    pat_end
