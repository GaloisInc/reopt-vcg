def cmovns1 : instruction :=
  definst "cmovns" $ do
    pattern fun (v_3048 : Mem) (v_3049 : reg (bv 32)) => do
      v_9064 <- getRegister sf;
      v_9067 <- evaluateAddress v_3048;
      v_9068 <- load v_9067 4;
      v_9069 <- getRegister v_3049;
      setRegister (lhs.of_reg v_3049) (mux (notBool_ (eq v_9064 (expression.bv_nat 1 1))) v_9068 v_9069);
      pure ()
    pat_end;
    pattern fun (v_3065 : Mem) (v_3066 : reg (bv 64)) => do
      v_9072 <- getRegister sf;
      v_9075 <- evaluateAddress v_3065;
      v_9076 <- load v_9075 8;
      v_9077 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3066) (mux (notBool_ (eq v_9072 (expression.bv_nat 1 1))) v_9076 v_9077);
      pure ()
    pat_end;
    pattern fun (v_3082 : Mem) (v_3084 : reg (bv 16)) => do
      v_9080 <- getRegister sf;
      v_9083 <- evaluateAddress v_3082;
      v_9084 <- load v_9083 2;
      v_9085 <- getRegister v_3084;
      setRegister (lhs.of_reg v_3084) (mux (notBool_ (eq v_9080 (expression.bv_nat 1 1))) v_9084 v_9085);
      pure ()
    pat_end
