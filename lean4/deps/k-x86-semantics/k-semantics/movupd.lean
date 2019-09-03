def movupd1 : instruction :=
  definst "movupd" $ do
    pattern fun (v_2611 : reg (bv 128)) (v_2612 : reg (bv 128)) => do
      v_4028 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2612) v_4028;
      pure ()
    pat_end;
    pattern fun (v_2603 : reg (bv 128)) (v_2602 : Mem) => do
      v_8644 <- evaluateAddress v_2602;
      v_8645 <- getRegister v_2603;
      store v_8644 v_8645 16;
      pure ()
    pat_end;
    pattern fun (v_2606 : Mem) (v_2607 : reg (bv 128)) => do
      v_8886 <- evaluateAddress v_2606;
      v_8887 <- load v_8886 16;
      setRegister (lhs.of_reg v_2607) v_8887;
      pure ()
    pat_end
