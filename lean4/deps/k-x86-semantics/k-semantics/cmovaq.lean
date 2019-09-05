def cmovaq1 : instruction :=
  definst "cmovaq" $ do
    pattern fun (v_2474 : reg (bv 64)) (v_2475 : reg (bv 64)) => do
      v_4138 <- getRegister cf;
      v_4141 <- getRegister zf;
      v_4145 <- getRegister v_2474;
      v_4146 <- getRegister v_2475;
      setRegister (lhs.of_reg v_2475) (mux (bit_and (notBool_ (eq v_4138 (expression.bv_nat 1 1))) (notBool_ (eq v_4141 (expression.bv_nat 1 1)))) v_4145 v_4146);
      pure ()
    pat_end;
    pattern fun (v_2469 : Mem) (v_2470 : reg (bv 64)) => do
      v_7822 <- getRegister cf;
      v_7825 <- getRegister zf;
      v_7829 <- evaluateAddress v_2469;
      v_7830 <- load v_7829 8;
      v_7831 <- getRegister v_2470;
      setRegister (lhs.of_reg v_2470) (mux (bit_and (notBool_ (eq v_7822 (expression.bv_nat 1 1))) (notBool_ (eq v_7825 (expression.bv_nat 1 1)))) v_7830 v_7831);
      pure ()
    pat_end
