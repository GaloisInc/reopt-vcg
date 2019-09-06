def movhps1 : instruction :=
  definst "movhps" $ do
    pattern fun (v_2552 : reg (bv 128)) (v_2551 : Mem) => do
      v_8463 <- evaluateAddress v_2551;
      v_8464 <- getRegister v_2552;
      store v_8463 (extract v_8464 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2555 : Mem) (v_2556 : reg (bv 128)) => do
      v_8725 <- evaluateAddress v_2555;
      v_8726 <- load v_8725 8;
      v_8727 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (concat v_8726 (extract v_8727 64 128));
      pure ()
    pat_end
