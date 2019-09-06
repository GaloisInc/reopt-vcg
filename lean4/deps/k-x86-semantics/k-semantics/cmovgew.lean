def cmovgew1 : instruction :=
  definst "cmovgew" $ do
    pattern fun (v_2692 : reg (bv 16)) (v_2693 : reg (bv 16)) => do
      v_4353 <- getRegister sf;
      v_4354 <- getRegister of;
      v_4356 <- getRegister v_2692;
      v_4357 <- getRegister v_2693;
      setRegister (lhs.of_reg v_2693) (mux (eq v_4353 v_4354) v_4356 v_4357);
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2685 : reg (bv 16)) => do
      v_7791 <- getRegister sf;
      v_7792 <- getRegister of;
      v_7794 <- evaluateAddress v_2684;
      v_7795 <- load v_7794 2;
      v_7796 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2685) (mux (eq v_7791 v_7792) v_7795 v_7796);
      pure ()
    pat_end
