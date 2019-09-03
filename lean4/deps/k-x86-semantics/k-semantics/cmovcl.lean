def cmovcl1 : instruction :=
  definst "cmovcl" $ do
    pattern fun (v_2506 : reg (bv 32)) (v_2507 : reg (bv 32)) => do
      v_4188 <- getRegister cf;
      v_4190 <- getRegister v_2506;
      v_4191 <- getRegister v_2507;
      setRegister (lhs.of_reg v_2507) (mux (eq v_4188 (expression.bv_nat 1 1)) v_4190 v_4191);
      pure ()
    pat_end;
    pattern fun (v_2502 : Mem) (v_2503 : reg (bv 32)) => do
      v_7914 <- getRegister cf;
      v_7916 <- evaluateAddress v_2502;
      v_7917 <- load v_7916 4;
      v_7918 <- getRegister v_2503;
      setRegister (lhs.of_reg v_2503) (mux (eq v_7914 (expression.bv_nat 1 1)) v_7917 v_7918);
      pure ()
    pat_end
