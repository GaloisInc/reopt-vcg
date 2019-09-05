def cmovcw1 : instruction :=
  definst "cmovcw" $ do
    pattern fun (v_2588 : reg (bv 16)) (v_2589 : reg (bv 16)) => do
      v_4272 <- getRegister cf;
      v_4274 <- getRegister v_2588;
      v_4275 <- getRegister v_2589;
      setRegister (lhs.of_reg v_2589) (mux (eq v_4272 (expression.bv_nat 1 1)) v_4274 v_4275);
      pure ()
    pat_end;
    pattern fun (v_2583 : Mem) (v_2584 : reg (bv 16)) => do
      v_7914 <- getRegister cf;
      v_7916 <- evaluateAddress v_2583;
      v_7917 <- load v_7916 2;
      v_7918 <- getRegister v_2584;
      setRegister (lhs.of_reg v_2584) (mux (eq v_7914 (expression.bv_nat 1 1)) v_7917 v_7918);
      pure ()
    pat_end
