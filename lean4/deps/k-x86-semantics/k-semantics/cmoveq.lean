def cmoveq1 : instruction :=
  definst "cmoveq" $ do
    pattern fun (v_2632 : reg (bv 64)) (v_2633 : reg (bv 64)) => do
      v_4298 <- getRegister zf;
      v_4299 <- getRegister v_2632;
      v_4300 <- getRegister v_2633;
      setRegister (lhs.of_reg v_2633) (mux v_4298 v_4299 v_4300);
      pure ()
    pat_end;
    pattern fun (v_2628 : Mem) (v_2629 : reg (bv 64)) => do
      v_7760 <- getRegister zf;
      v_7761 <- evaluateAddress v_2628;
      v_7762 <- load v_7761 8;
      v_7763 <- getRegister v_2629;
      setRegister (lhs.of_reg v_2629) (mux v_7760 v_7762 v_7763);
      pure ()
    pat_end
