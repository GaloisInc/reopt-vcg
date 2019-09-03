def cmovleq1 : instruction :=
  definst "cmovleq" $ do
    pattern fun (v_2664 : reg (bv 64)) (v_2665 : reg (bv 64)) => do
      v_4380 <- getRegister zf;
      v_4382 <- getRegister sf;
      v_4384 <- getRegister of;
      v_4389 <- getRegister v_2664;
      v_4390 <- getRegister v_2665;
      setRegister (lhs.of_reg v_2665) (mux (bit_or (eq v_4380 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4382 (expression.bv_nat 1 1)) (eq v_4384 (expression.bv_nat 1 1))))) v_4389 v_4390);
      pure ()
    pat_end;
    pattern fun (v_2655 : Mem) (v_2656 : reg (bv 64)) => do
      v_8047 <- getRegister zf;
      v_8049 <- getRegister sf;
      v_8051 <- getRegister of;
      v_8056 <- evaluateAddress v_2655;
      v_8057 <- load v_8056 8;
      v_8058 <- getRegister v_2656;
      setRegister (lhs.of_reg v_2656) (mux (bit_or (eq v_8047 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8049 (expression.bv_nat 1 1)) (eq v_8051 (expression.bv_nat 1 1))))) v_8057 v_8058);
      pure ()
    pat_end
