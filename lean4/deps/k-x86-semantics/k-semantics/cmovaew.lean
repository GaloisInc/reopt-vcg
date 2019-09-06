def cmovaew1 : instruction :=
  definst "cmovaew" $ do
    pattern fun (v_2482 : reg (bv 16)) (v_2483 : reg (bv 16)) => do
      v_4138 <- getRegister cf;
      v_4140 <- getRegister v_2482;
      v_4141 <- getRegister v_2483;
      setRegister (lhs.of_reg v_2483) (mux (notBool_ v_4138) v_4140 v_4141);
      pure ()
    pat_end;
    pattern fun (v_2478 : Mem) (v_2479 : reg (bv 16)) => do
      v_7654 <- getRegister cf;
      v_7656 <- evaluateAddress v_2478;
      v_7657 <- load v_7656 2;
      v_7658 <- getRegister v_2479;
      setRegister (lhs.of_reg v_2479) (mux (notBool_ v_7654) v_7657 v_7658);
      pure ()
    pat_end
