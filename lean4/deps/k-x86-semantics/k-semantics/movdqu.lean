def movdqu1 : instruction :=
  definst "movdqu" $ do
    pattern fun (v_2457 : reg (bv 128)) (v_2458 : reg (bv 128)) => do
      v_3881 <- getRegister v_2457;
      setRegister (lhs.of_reg v_2458) v_3881;
      pure ()
    pat_end;
    pattern fun (v_2450 : reg (bv 128)) (v_2449 : Mem) => do
      v_8563 <- evaluateAddress v_2449;
      v_8564 <- getRegister v_2450;
      store v_8563 v_8564 16;
      pure ()
    pat_end;
    pattern fun (v_2453 : Mem) (v_2454 : reg (bv 128)) => do
      v_8825 <- evaluateAddress v_2453;
      v_8826 <- load v_8825 16;
      setRegister (lhs.of_reg v_2454) v_8826;
      pure ()
    pat_end
