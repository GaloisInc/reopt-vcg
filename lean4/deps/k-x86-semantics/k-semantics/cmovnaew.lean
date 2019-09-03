def cmovnaew1 : instruction :=
  definst "cmovnaew" $ do
    pattern fun (v_2748 : reg (bv 16)) (v_2749 : reg (bv 16)) => do
      v_4494 <- getRegister cf;
      v_4496 <- getRegister v_2748;
      v_4497 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2749) (mux (eq v_4494 (expression.bv_nat 1 1)) v_4496 v_4497);
      pure ()
    pat_end;
    pattern fun (v_2742 : Mem) (v_2744 : reg (bv 16)) => do
      v_8096 <- getRegister cf;
      v_8098 <- evaluateAddress v_2742;
      v_8099 <- load v_8098 2;
      v_8100 <- getRegister v_2744;
      setRegister (lhs.of_reg v_2744) (mux (eq v_8096 (expression.bv_nat 1 1)) v_8099 v_8100);
      pure ()
    pat_end
