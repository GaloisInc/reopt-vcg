def cmovngew1 : instruction :=
  definst "cmovngew" $ do
    pattern fun (v_2910 : reg (bv 16)) (v_2911 : reg (bv 16)) => do
      v_4715 <- getRegister sf;
      v_4717 <- getRegister of;
      v_4721 <- getRegister v_2910;
      v_4722 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2911) (mux (notBool_ (eq (eq v_4715 (expression.bv_nat 1 1)) (eq v_4717 (expression.bv_nat 1 1)))) v_4721 v_4722);
      pure ()
    pat_end;
    pattern fun (v_2904 : Mem) (v_2906 : reg (bv 16)) => do
      v_8263 <- getRegister sf;
      v_8265 <- getRegister of;
      v_8269 <- evaluateAddress v_2904;
      v_8270 <- load v_8269 2;
      v_8271 <- getRegister v_2906;
      setRegister (lhs.of_reg v_2906) (mux (notBool_ (eq (eq v_8263 (expression.bv_nat 1 1)) (eq v_8265 (expression.bv_nat 1 1)))) v_8270 v_8271);
      pure ()
    pat_end
