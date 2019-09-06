def cmovew1 : instruction :=
  definst "cmovew" $ do
    pattern fun (v_2641 : reg (bv 16)) (v_2642 : reg (bv 16)) => do
      v_4307 <- getRegister zf;
      v_4308 <- getRegister v_2641;
      v_4309 <- getRegister v_2642;
      setRegister (lhs.of_reg v_2642) (mux v_4307 v_4308 v_4309);
      pure ()
    pat_end;
    pattern fun (v_2637 : Mem) (v_2638 : reg (bv 16)) => do
      v_7766 <- getRegister zf;
      v_7767 <- evaluateAddress v_2637;
      v_7768 <- load v_7767 2;
      v_7769 <- getRegister v_2638;
      setRegister (lhs.of_reg v_2638) (mux v_7766 v_7768 v_7769);
      pure ()
    pat_end
