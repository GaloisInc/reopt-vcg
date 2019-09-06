def cmovbew1 : instruction :=
  definst "cmovbew" $ do
    pattern fun (v_2560 : reg (bv 16)) (v_2561 : reg (bv 16)) => do
      v_4224 <- getRegister cf;
      v_4225 <- getRegister zf;
      v_4227 <- getRegister v_2560;
      v_4228 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2561) (mux (bit_or v_4224 v_4225) v_4227 v_4228);
      pure ()
    pat_end;
    pattern fun (v_2552 : Mem) (v_2553 : reg (bv 16)) => do
      v_7710 <- getRegister cf;
      v_7711 <- getRegister zf;
      v_7713 <- evaluateAddress v_2552;
      v_7714 <- load v_7713 2;
      v_7715 <- getRegister v_2553;
      setRegister (lhs.of_reg v_2553) (mux (bit_or v_7710 v_7711) v_7714 v_7715);
      pure ()
    pat_end
