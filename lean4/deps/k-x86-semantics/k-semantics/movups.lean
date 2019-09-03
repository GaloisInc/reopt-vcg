def movups1 : instruction :=
  definst "movups" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) => do
      v_4038 <- getRegister v_2624;
      setRegister (lhs.of_reg v_2625) v_4038;
      pure ()
    pat_end;
    pattern fun (v_2616 : reg (bv 128)) (v_2615 : Mem) => do
      v_8648 <- evaluateAddress v_2615;
      v_8649 <- getRegister v_2616;
      store v_8648 v_8649 16;
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2620 : reg (bv 128)) => do
      v_8889 <- evaluateAddress v_2619;
      v_8890 <- load v_8889 16;
      setRegister (lhs.of_reg v_2620) v_8890;
      pure ()
    pat_end
