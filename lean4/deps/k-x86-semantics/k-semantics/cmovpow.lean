def cmovpow1 : instruction :=
  definst "cmovpow" $ do
    pattern fun (v_3213 : reg (bv 16)) (v_3214 : reg (bv 16)) => do
      v_5109 <- getRegister pf;
      v_5112 <- getRegister v_3213;
      v_5113 <- getRegister v_3214;
      setRegister (lhs.of_reg v_3214) (mux (notBool_ (eq v_5109 (expression.bv_nat 1 1))) v_5112 v_5113);
      pure ()
    pat_end;
    pattern fun (v_3207 : Mem) (v_3209 : reg (bv 16)) => do
      v_8552 <- getRegister pf;
      v_8555 <- evaluateAddress v_3207;
      v_8556 <- load v_8555 2;
      v_8557 <- getRegister v_3209;
      setRegister (lhs.of_reg v_3209) (mux (notBool_ (eq v_8552 (expression.bv_nat 1 1))) v_8556 v_8557);
      pure ()
    pat_end
