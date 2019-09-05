def vpand1 : instruction :=
  definst "vpand" $ do
    pattern fun (v_2580 : Mem) (v_2581 : reg (bv 128)) (v_2582 : reg (bv 128)) => do
      v_14419 <- getRegister v_2581;
      v_14420 <- evaluateAddress v_2580;
      v_14421 <- load v_14420 16;
      setRegister (lhs.of_reg v_2582) (bv_and v_14419 v_14421);
      pure ()
    pat_end;
    pattern fun (v_2591 : Mem) (v_2592 : reg (bv 256)) (v_2593 : reg (bv 256)) => do
      v_14424 <- getRegister v_2592;
      v_14425 <- evaluateAddress v_2591;
      v_14426 <- load v_14425 32;
      setRegister (lhs.of_reg v_2593) (bv_and v_14424 v_14426);
      pure ()
    pat_end
