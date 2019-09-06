def cmovbeq1 : instruction :=
  definst "cmovbeq" $ do
    pattern fun (v_2543 : reg (bv 64)) (v_2544 : reg (bv 64)) => do
      v_4208 <- getRegister cf;
      v_4209 <- getRegister zf;
      v_4211 <- getRegister v_2543;
      v_4212 <- getRegister v_2544;
      setRegister (lhs.of_reg v_2544) (mux (bit_or v_4208 v_4209) v_4211 v_4212);
      pure ()
    pat_end;
    pattern fun (v_2535 : Mem) (v_2536 : reg (bv 64)) => do
      v_7701 <- getRegister cf;
      v_7702 <- getRegister zf;
      v_7704 <- evaluateAddress v_2535;
      v_7705 <- load v_7704 8;
      v_7706 <- getRegister v_2536;
      setRegister (lhs.of_reg v_2536) (mux (bit_or v_7701 v_7702) v_7705 v_7706);
      pure ()
    pat_end
