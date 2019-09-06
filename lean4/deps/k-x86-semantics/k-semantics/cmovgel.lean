def cmovgel1 : instruction :=
  definst "cmovgel" $ do
    pattern fun (v_2661 : reg (bv 32)) (v_2662 : reg (bv 32)) => do
      v_4321 <- getRegister sf;
      v_4322 <- getRegister of;
      v_4324 <- getRegister v_2661;
      v_4325 <- getRegister v_2662;
      setRegister (lhs.of_reg v_2662) (mux (eq v_4321 v_4322) v_4324 v_4325);
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2653 : reg (bv 32)) => do
      v_7773 <- getRegister sf;
      v_7774 <- getRegister of;
      v_7776 <- evaluateAddress v_2650;
      v_7777 <- load v_7776 4;
      v_7778 <- getRegister v_2653;
      setRegister (lhs.of_reg v_2653) (mux (eq v_7773 v_7774) v_7777 v_7778);
      pure ()
    pat_end
