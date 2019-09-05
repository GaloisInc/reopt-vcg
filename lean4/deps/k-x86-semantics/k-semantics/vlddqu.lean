def vlddqu1 : instruction :=
  definst "vlddqu" $ do
    pattern fun (v_2549 : Mem) (v_2550 : reg (bv 128)) => do
      v_9750 <- evaluateAddress v_2549;
      v_9751 <- load v_9750 16;
      setRegister (lhs.of_reg v_2550) v_9751;
      pure ()
    pat_end;
    pattern fun (v_2553 : Mem) (v_2554 : reg (bv 256)) => do
      v_9753 <- evaluateAddress v_2553;
      v_9754 <- load v_9753 32;
      setRegister (lhs.of_reg v_2554) v_9754;
      pure ()
    pat_end
