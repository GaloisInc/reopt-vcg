def cmovbl1 : instruction :=
  definst "cmovbl" $ do
    pattern fun (v_2572 : reg (bv 32)) (v_2573 : reg (bv 32)) => do
      v_4235 <- getRegister cf;
      v_4236 <- getRegister v_2572;
      v_4237 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2573) (mux v_4235 v_4236 v_4237);
      pure ()
    pat_end;
    pattern fun (v_2565 : Mem) (v_2568 : reg (bv 32)) => do
      v_7718 <- getRegister cf;
      v_7719 <- evaluateAddress v_2565;
      v_7720 <- load v_7719 4;
      v_7721 <- getRegister v_2568;
      setRegister (lhs.of_reg v_2568) (mux v_7718 v_7720 v_7721);
      pure ()
    pat_end
