def cmovaew1 : instruction :=
  definst "cmovaew" $ do
    pattern fun (v_2456 : reg (bv 16)) (v_2457 : reg (bv 16)) => do
      v_4112 <- getRegister cf;
      v_4115 <- getRegister v_2456;
      v_4116 <- getRegister v_2457;
      setRegister (lhs.of_reg v_2457) (mux (notBool_ (eq v_4112 (expression.bv_nat 1 1))) v_4115 v_4116);
      pure ()
    pat_end;
    pattern fun (v_2451 : Mem) (v_2452 : reg (bv 16)) => do
      v_7802 <- getRegister cf;
      v_7805 <- evaluateAddress v_2451;
      v_7806 <- load v_7805 2;
      v_7807 <- getRegister v_2452;
      setRegister (lhs.of_reg v_2452) (mux (notBool_ (eq v_7802 (expression.bv_nat 1 1))) v_7806 v_7807);
      pure ()
    pat_end
