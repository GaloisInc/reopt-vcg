def movupd1 : instruction :=
  definst "movupd" $ do
    pattern fun (v_2699 : reg (bv 128)) (v_2700 : reg (bv 128)) => do
      v_4119 <- getRegister v_2699;
      setRegister (lhs.of_reg v_2700) v_4119;
      pure ()
    pat_end;
    pattern fun (v_2692 : reg (bv 128)) (v_2691 : Mem) => do
      v_8514 <- evaluateAddress v_2691;
      v_8515 <- getRegister v_2692;
      store v_8514 v_8515 16;
      pure ()
    pat_end;
    pattern fun (v_2695 : Mem) (v_2696 : reg (bv 128)) => do
      v_8756 <- evaluateAddress v_2695;
      v_8757 <- load v_8756 16;
      setRegister (lhs.of_reg v_2696) v_8757;
      pure ()
    pat_end
