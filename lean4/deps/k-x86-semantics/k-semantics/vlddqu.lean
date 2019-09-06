def vlddqu1 : instruction :=
  definst "vlddqu" $ do
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 128)) => do
      v_9777 <- evaluateAddress v_2574;
      v_9778 <- load v_9777 16;
      setRegister (lhs.of_reg v_2575) v_9778;
      pure ()
    pat_end;
    pattern fun (v_2578 : Mem) (v_2579 : reg (bv 256)) => do
      v_9780 <- evaluateAddress v_2578;
      v_9781 <- load v_9780 32;
      setRegister (lhs.of_reg v_2579) v_9781;
      pure ()
    pat_end
