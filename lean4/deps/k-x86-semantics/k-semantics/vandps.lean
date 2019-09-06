def vandps1 : instruction :=
  definst "vandps" $ do
    pattern fun (v_2829 : Mem) (v_2832 : reg (bv 128)) (v_2833 : reg (bv 128)) => do
      v_9453 <- getRegister v_2832;
      v_9454 <- evaluateAddress v_2829;
      v_9455 <- load v_9454 16;
      setRegister (lhs.of_reg v_2833) (bv_and v_9453 v_9455);
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 256)) (v_2842 : reg (bv 256)) => do
      v_9458 <- getRegister v_2841;
      v_9459 <- evaluateAddress v_2840;
      v_9460 <- load v_9459 32;
      setRegister (lhs.of_reg v_2842) (bv_and v_9458 v_9460);
      pure ()
    pat_end
