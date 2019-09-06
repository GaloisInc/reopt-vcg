def cmovgeq1 : instruction :=
  definst "cmovgeq" $ do
    pattern fun (v_2675 : reg (bv 64)) (v_2676 : reg (bv 64)) => do
      v_4337 <- getRegister sf;
      v_4338 <- getRegister of;
      v_4340 <- getRegister v_2675;
      v_4341 <- getRegister v_2676;
      setRegister (lhs.of_reg v_2676) (mux (eq v_4337 v_4338) v_4340 v_4341);
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) (v_2668 : reg (bv 64)) => do
      v_7782 <- getRegister sf;
      v_7783 <- getRegister of;
      v_7785 <- evaluateAddress v_2667;
      v_7786 <- load v_7785 8;
      v_7787 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2668) (mux (eq v_7782 v_7783) v_7786 v_7787);
      pure ()
    pat_end
