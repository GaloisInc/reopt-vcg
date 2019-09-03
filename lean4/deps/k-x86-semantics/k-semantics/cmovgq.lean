def cmovgq1 : instruction :=
  definst "cmovgq" $ do
    pattern fun (v_2632 : reg (bv 64)) (v_2633 : reg (bv 64)) => do
      v_4332 <- getRegister zf;
      v_4335 <- getRegister sf;
      v_4337 <- getRegister of;
      v_4341 <- getRegister v_2632;
      v_4342 <- getRegister v_2633;
      setRegister (lhs.of_reg v_2633) (mux (bit_and (notBool_ (eq v_4332 (expression.bv_nat 1 1))) (eq (eq v_4335 (expression.bv_nat 1 1)) (eq v_4337 (expression.bv_nat 1 1)))) v_4341 v_4342);
      pure ()
    pat_end;
    pattern fun (v_2628 : Mem) (v_2629 : reg (bv 64)) => do
      v_7976 <- getRegister zf;
      v_7979 <- getRegister sf;
      v_7981 <- getRegister of;
      v_7985 <- evaluateAddress v_2628;
      v_7986 <- load v_7985 8;
      v_7987 <- getRegister v_2629;
      setRegister (lhs.of_reg v_2629) (mux (bit_and (notBool_ (eq v_7976 (expression.bv_nat 1 1))) (eq (eq v_7979 (expression.bv_nat 1 1)) (eq v_7981 (expression.bv_nat 1 1)))) v_7986 v_7987);
      pure ()
    pat_end
