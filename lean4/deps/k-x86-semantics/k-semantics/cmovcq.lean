def cmovcq1 : instruction :=
  definst "cmovcq" $ do
    pattern fun (v_2605 : reg (bv 64)) (v_2606 : reg (bv 64)) => do
      v_4271 <- getRegister cf;
      v_4272 <- getRegister v_2605;
      v_4273 <- getRegister v_2606;
      setRegister (lhs.of_reg v_2606) (mux v_4271 v_4272 v_4273);
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 64)) => do
      v_7742 <- getRegister cf;
      v_7743 <- evaluateAddress v_2601;
      v_7744 <- load v_7743 8;
      v_7745 <- getRegister v_2602;
      setRegister (lhs.of_reg v_2602) (mux v_7742 v_7744 v_7745);
      pure ()
    pat_end
