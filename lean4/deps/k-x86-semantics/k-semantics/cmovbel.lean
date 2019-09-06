def cmovbel1 : instruction :=
  definst "cmovbel" $ do
    pattern fun (v_2529 : reg (bv 32)) (v_2530 : reg (bv 32)) => do
      v_4192 <- getRegister cf;
      v_4193 <- getRegister zf;
      v_4195 <- getRegister v_2529;
      v_4196 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2530) (mux (bit_or v_4192 v_4193) v_4195 v_4196);
      pure ()
    pat_end;
    pattern fun (v_2518 : Mem) (v_2521 : reg (bv 32)) => do
      v_7692 <- getRegister cf;
      v_7693 <- getRegister zf;
      v_7695 <- evaluateAddress v_2518;
      v_7696 <- load v_7695 4;
      v_7697 <- getRegister v_2521;
      setRegister (lhs.of_reg v_2521) (mux (bit_or v_7692 v_7693) v_7696 v_7697);
      pure ()
    pat_end
