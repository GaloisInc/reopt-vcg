def cmovge1 : instruction :=
  definst "cmovge" $ do
    pattern fun (v_2619 : Mem) (v_2622 : reg (bv 32)) => do
      v_8973 <- getRegister sf;
      v_8975 <- getRegister of;
      v_8978 <- evaluateAddress v_2619;
      v_8979 <- load v_8978 4;
      v_8980 <- getRegister v_2622;
      setRegister (lhs.of_reg v_2622) (mux (eq (eq v_8973 (expression.bv_nat 1 1)) (eq v_8975 (expression.bv_nat 1 1))) v_8979 v_8980);
      pure ()
    pat_end;
    pattern fun (v_2637 : Mem) (v_2636 : reg (bv 64)) => do
      v_8983 <- getRegister sf;
      v_8985 <- getRegister of;
      v_8988 <- evaluateAddress v_2637;
      v_8989 <- load v_8988 8;
      v_8990 <- getRegister v_2636;
      setRegister (lhs.of_reg v_2636) (mux (eq (eq v_8983 (expression.bv_nat 1 1)) (eq v_8985 (expression.bv_nat 1 1))) v_8989 v_8990);
      pure ()
    pat_end;
    pattern fun (v_2654 : Mem) (v_2653 : reg (bv 16)) => do
      v_8993 <- getRegister sf;
      v_8995 <- getRegister of;
      v_8998 <- evaluateAddress v_2654;
      v_8999 <- load v_8998 2;
      v_9000 <- getRegister v_2653;
      setRegister (lhs.of_reg v_2653) (mux (eq (eq v_8993 (expression.bv_nat 1 1)) (eq v_8995 (expression.bv_nat 1 1))) v_8999 v_9000);
      pure ()
    pat_end
