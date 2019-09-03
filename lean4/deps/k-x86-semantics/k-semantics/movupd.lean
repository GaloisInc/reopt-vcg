def movupd1 : instruction :=
  definst "movupd" $ do
    pattern fun (v_2623 : reg (bv 128)) (v_2624 : reg (bv 128)) => do
      v_4041 <- getRegister v_2623;
      setRegister (lhs.of_reg v_2624) v_4041;
      pure ()
    pat_end;
    pattern fun (v_2616 : reg (bv 128)) (v_2615 : Mem) => do
      v_8623 <- evaluateAddress v_2615;
      v_8624 <- getRegister v_2616;
      store v_8623 v_8624 16;
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2620 : reg (bv 128)) => do
      v_8865 <- evaluateAddress v_2619;
      v_8866 <- load v_8865 16;
      setRegister (lhs.of_reg v_2620) v_8866;
      pure ()
    pat_end
