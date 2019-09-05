def cmovbl1 : instruction :=
  definst "cmovbl" $ do
    pattern fun (v_2545 : reg (bv 32)) (v_2546 : reg (bv 32)) => do
      v_4222 <- getRegister cf;
      v_4224 <- getRegister v_2545;
      v_4225 <- getRegister v_2546;
      setRegister (lhs.of_reg v_2546) (mux (eq v_4222 (expression.bv_nat 1 1)) v_4224 v_4225);
      pure ()
    pat_end;
    pattern fun (v_2538 : Mem) (v_2541 : reg (bv 32)) => do
      v_7879 <- getRegister cf;
      v_7881 <- evaluateAddress v_2538;
      v_7882 <- load v_7881 4;
      v_7883 <- getRegister v_2541;
      setRegister (lhs.of_reg v_2541) (mux (eq v_7879 (expression.bv_nat 1 1)) v_7882 v_7883);
      pure ()
    pat_end
