def setng1 : instruction :=
  definst "setng" $ do
    pattern fun (v_2654 : reg (bv 8)) => do
      v_4136 <- getRegister zf;
      v_4137 <- getRegister sf;
      v_4138 <- getRegister of;
      setRegister (lhs.of_reg v_2654) (mux (bit_or v_4136 (notBool_ (eq v_4137 v_4138))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2647 : Mem) => do
      v_7984 <- evaluateAddress v_2647;
      v_7985 <- getRegister zf;
      v_7986 <- getRegister sf;
      v_7987 <- getRegister of;
      store v_7984 (mux (bit_or v_7985 (notBool_ (eq v_7986 v_7987))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
