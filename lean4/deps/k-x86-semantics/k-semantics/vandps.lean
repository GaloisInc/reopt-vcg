def vandps1 : instruction :=
  definst "vandps" $ do
    pattern fun (v_2804 : Mem) (v_2805 : reg (bv 128)) (v_2806 : reg (bv 128)) => do
      v_9426 <- getRegister v_2805;
      v_9427 <- evaluateAddress v_2804;
      v_9428 <- load v_9427 16;
      setRegister (lhs.of_reg v_2806) (bv_and v_9426 v_9428);
      pure ()
    pat_end;
    pattern fun (v_2815 : Mem) (v_2816 : reg (bv 256)) (v_2817 : reg (bv 256)) => do
      v_9431 <- getRegister v_2816;
      v_9432 <- evaluateAddress v_2815;
      v_9433 <- load v_9432 32;
      setRegister (lhs.of_reg v_2817) (bv_and v_9431 v_9433);
      pure ()
    pat_end
