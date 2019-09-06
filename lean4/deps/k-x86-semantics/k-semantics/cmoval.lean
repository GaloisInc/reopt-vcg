def cmoval1 : instruction :=
  definst "cmoval" $ do
    pattern fun (v_2494 : reg (bv 32)) (v_2495 : reg (bv 32)) => do
      v_4148 <- getRegister cf;
      v_4150 <- getRegister zf;
      v_4153 <- getRegister v_2494;
      v_4154 <- getRegister v_2495;
      setRegister (lhs.of_reg v_2495) (mux (bit_and (notBool_ v_4148) (notBool_ v_4150)) v_4153 v_4154);
      pure ()
    pat_end;
    pattern fun (v_2487 : Mem) (v_2490 : reg (bv 32)) => do
      v_7661 <- getRegister cf;
      v_7663 <- getRegister zf;
      v_7666 <- evaluateAddress v_2487;
      v_7667 <- load v_7666 4;
      v_7668 <- getRegister v_2490;
      setRegister (lhs.of_reg v_2490) (mux (bit_and (notBool_ v_7661) (notBool_ v_7663)) v_7667 v_7668);
      pure ()
    pat_end
