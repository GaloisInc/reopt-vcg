def cmovaeq1 : instruction :=
  definst "cmovaeq" $ do
    pattern fun (v_2473 : reg (bv 64)) (v_2474 : reg (bv 64)) => do
      v_4128 <- getRegister cf;
      v_4130 <- getRegister v_2473;
      v_4131 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2474) (mux (notBool_ v_4128) v_4130 v_4131);
      pure ()
    pat_end;
    pattern fun (v_2469 : Mem) (v_2470 : reg (bv 64)) => do
      v_7647 <- getRegister cf;
      v_7649 <- evaluateAddress v_2469;
      v_7650 <- load v_7649 8;
      v_7651 <- getRegister v_2470;
      setRegister (lhs.of_reg v_2470) (mux (notBool_ v_7647) v_7650 v_7651);
      pure ()
    pat_end
