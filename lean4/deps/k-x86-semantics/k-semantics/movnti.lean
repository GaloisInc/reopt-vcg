def movnti1 : instruction :=
  definst "movnti" $ do
    pattern fun (v_2555 : reg (bv 32)) (v_2554 : Mem) => do
      v_8598 <- evaluateAddress v_2554;
      v_8599 <- getRegister v_2555;
      store v_8598 v_8599 4;
      pure ()
    pat_end;
    pattern fun (v_2559 : reg (bv 64)) (v_2558 : Mem) => do
      v_8601 <- evaluateAddress v_2558;
      v_8602 <- getRegister v_2559;
      store v_8601 v_8602 8;
      pure ()
    pat_end
