def cmovnbw1 : instruction :=
  definst "cmovnbw" $ do
    pattern fun (v_2879 : reg (bv 16)) (v_2880 : reg (bv 16)) => do
      v_4661 <- getRegister cf;
      v_4664 <- getRegister v_2879;
      v_4665 <- getRegister v_2880;
      setRegister (lhs.of_reg v_2880) (mux (notBool_ (eq v_4661 (expression.bv_nat 1 1))) v_4664 v_4665);
      pure ()
    pat_end;
    pattern fun (v_2874 : Mem) (v_2875 : reg (bv 16)) => do
      v_8198 <- getRegister cf;
      v_8201 <- evaluateAddress v_2874;
      v_8202 <- load v_8201 2;
      v_8203 <- getRegister v_2875;
      setRegister (lhs.of_reg v_2875) (mux (notBool_ (eq v_8198 (expression.bv_nat 1 1))) v_8202 v_8203);
      pure ()
    pat_end
