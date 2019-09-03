def vlddqu1 : instruction :=
  definst "vlddqu" $ do
    pattern fun (v_2485 : Mem) (v_2486 : reg (bv 128)) => do
      v_9866 <- evaluateAddress v_2485;
      v_9867 <- load v_9866 16;
      setRegister (lhs.of_reg v_2486) v_9867;
      pure ()
    pat_end;
    pattern fun (v_2489 : Mem) (v_2490 : reg (bv 256)) => do
      v_9869 <- evaluateAddress v_2489;
      v_9870 <- load v_9869 32;
      setRegister (lhs.of_reg v_2490) v_9870;
      pure ()
    pat_end
