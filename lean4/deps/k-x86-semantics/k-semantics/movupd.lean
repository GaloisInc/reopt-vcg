def movupd1 : instruction :=
  definst "movupd" $ do
    pattern fun (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_4092 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2675) v_4092;
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 128)) (v_2665 : Mem) => do
      v_8487 <- evaluateAddress v_2665;
      v_8488 <- getRegister v_2666;
      store v_8487 v_8488 16;
      pure ()
    pat_end;
    pattern fun (v_2669 : Mem) (v_2670 : reg (bv 128)) => do
      v_8729 <- evaluateAddress v_2669;
      v_8730 <- load v_8729 16;
      setRegister (lhs.of_reg v_2670) v_8730;
      pure ()
    pat_end
